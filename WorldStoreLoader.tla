----------------------------- MODULE WorldStoreLoader ----------------------------
(********************************************************************************)
(* This module specifies the behavior of the WorldStore loader. It includes a   *)
(* safety invariant, but does not describe any liveness properties.             *)
(*                                                                              *)
(* We make the following assumptions (% denotes that the assumption does not    *)
(* match reality):                                                              *)
(*   - % There is a fixed set of requests in the system (Requests).             *)
(*   - The database is a key value store.                                       *)
(*     - MySQL can be treated as a key value store where the set of keys is     *)
(*       predetermined by the schema.                                           *)
(*     - % Each update only affects one key.                                    *)
(*   - The database has a version that we model as a natural number.            *)
(*     - This version is incremented on every update to the database.           *)
(*     - % There exists some maximum version after which the database will      *)
(*         accept no more updates.                                              *)
(*     - On each update to the database, an invalidation stream                 *)
(*       (InvalidationTopicsForVersion) will be updated so that the             *)
(*       invalidation topics for the new database version has a non-empty       *)
(*       intersection with the topics associated with the updated key. This     *)
(*       abstraction represents the work of the WorldStore invalidator.         *)
(*   - % There is a single database instance that has no replicas.              *)
(*     - % We assume this database instance does not fail                       *)
(*     - We pretend this database maintains a snapshot of its data for each     *)
(*       version. This is only used to enforce the safety invariant, so none of *)
(*       behaviors in the specification take advantage of these snapshots.      *)
(*   - There can exist multiple topic version cache replicas                    *)
(*     (TopicVersionCacheInstance) and multiple data cache replicas             *)
(*     (DataCacheInstance).                                                     *)
(*   - % Data on the topic version cache and data cache are not sharded.        *)
(*   - There can exist multiple cache invalidators.                             *)
(********************************************************************************)

EXTENDS Types, 
        TopicVersionCacheOperators, 
        DataCacheOperators, 
        DatabaseOperators, 
        RequestOperators

VARIABLE StateForRequest,
         StateForCacheInvalidator,         
         InvalidationTopicsForVersion,
         StateForTopicVersionCacheInstance,
         StateForDataCacheInstance,
         StateForDatabase

UpdateRequestState(r, newRequestState) == StateForRequest' = [StateForRequest EXCEPT ![r] = newRequestState]
UpdateTopicVersionCacheState(tvc, newTopicVersionCacheState) == 
  StateForTopicVersionCacheInstance' = [StateForTopicVersionCacheInstance EXCEPT ![tvc] = newTopicVersionCacheState]
UpdateDataCacheState(dc, newDataCacheState) == StateForDataCacheInstance' = [StateForDataCacheInstance EXCEPT ![dc] = newDataCacheState]
UpdateCacheInvalidatorState(ci, newVersion) == StateForCacheInvalidator' = [StateForCacheInvalidator EXCEPT ![ci] = newVersion]
UpdateDatabaseState(newDatabaseState) == StateForDatabase' = newDatabaseState

StartRequest(r, key, requestVersion) ==
  LET requestState == StateForRequest[r] IN 
  LET newRequestState == StartedRequestState(key, requestVersion) IN
  /\ requestState.type = IdleType
  /\ UpdateRequestState(r, newRequestState)
  /\ UNCHANGED <<StateForCacheInvalidator, InvalidationTopicsForVersion, StateForTopicVersionCacheInstance, StateForDataCacheInstance, StateForDatabase>>

RequestCaches(r) == 
  LET requestState == StateForRequest[r] IN 
  LET newRequestState == CachesRequestedRequestState(requestState) IN
  /\ requestState.type = StartedType
  /\ UpdateRequestState(r, newRequestState)
  /\ UNCHANGED <<StateForCacheInvalidator, InvalidationTopicsForVersion, StateForTopicVersionCacheInstance, StateForDataCacheInstance, StateForDatabase>>

HandleTopicVersionCacheRequest(r, tvc) ==
  LET requestState == StateForRequest[r] IN 
  /\ requestState.type = CachesRequestedType
  /\ requestState.maybeTopicVersionCacheResponse = NoneVal
  /\ LET topicVersionCacheState == StateForTopicVersionCacheInstance[tvc] IN
     LET topicsForKey == TopicsForKey[requestState.key] IN
     LET newTopicVersionCacheState == UpdatedTopicVersionCacheForRequest(topicVersionCacheState, topicsForKey)  IN
     LET topicVersionCacheResponse == GetTopicVersionCacheResponse(newTopicVersionCacheState, topicsForKey) IN
     LET newRequestState == [requestState EXCEPT !.maybeTopicVersionCacheResponse = SomeVal(topicVersionCacheResponse)] IN
     /\ UpdateTopicVersionCacheState(tvc, newTopicVersionCacheState)
     /\ UpdateRequestState(r, newRequestState)
  /\ UNCHANGED <<StateForCacheInvalidator, InvalidationTopicsForVersion, StateForDataCacheInstance, StateForDatabase>>

HandleDataCacheRequest(r, dc) == 
  LET requestState == StateForRequest[r] IN 
  /\ requestState.type = CachesRequestedType
  /\ requestState.maybeDataCacheResponse = NoneVal
  /\ LET dataCacheState == StateForDataCacheInstance[dc] IN
     LET dataCacheResponse == GetDataCacheResponse(dataCacheState, requestState.key)  IN
     LET newRequestState == [requestState EXCEPT !.maybeDataCacheResponse = SomeVal(dataCacheResponse)] IN
     UpdateRequestState(r, newRequestState)
  /\ UNCHANGED <<StateForCacheInvalidator, InvalidationTopicsForVersion, StateForTopicVersionCacheInstance, StateForDataCacheInstance, StateForDatabase>>
  
HandleCacheResponses(r) == 
  LET requestState == StateForRequest[r] IN 
  /\ requestState.type = CachesRequestedType
  /\ requestState.maybeTopicVersionCacheResponse /= NoneVal
  /\ requestState.maybeDataCacheResponse /= NoneVal
  /\ LET topicVersionCacheResponse == requestState.maybeTopicVersionCacheResponse.value IN
     LET dataCacheResponse == requestState.maybeDataCacheResponse.value IN
     LET newRequestState ==
       IF topicVersionCacheResponse = NoneVal THEN 
         CacheMissRequestState(requestState, NoneVal)
       ELSE
         IF \/ dataCacheResponse = NoneVal
            \/ topicVersionCacheResponse.value.maxTopicVersion > dataCacheResponse.value.version 
            \/ topicVersionCacheResponse.value.cacheVersion < requestState.requestVersion THEN
           CacheMissRequestState(requestState, SomeVal(topicVersionCacheResponse.value.cacheVersion))
         ELSE
           CompletedRequestState(requestState, dataCacheResponse.value.data) IN
       UpdateRequestState(r, newRequestState)
  /\ UNCHANGED <<StateForCacheInvalidator, InvalidationTopicsForVersion, StateForTopicVersionCacheInstance, StateForDataCacheInstance, StateForDatabase>>
  
HandleDatabaseRequest(r) == 
  LET requestState == StateForRequest[r] IN 
  /\ requestState.type = CacheMissType
  /\ LET databaseResponse == GetDatabaseResponse(StateForDatabase, requestState.key) IN
     LET newRequestState == DatabaseRespondedRequestState(requestState, databaseResponse) IN
     UpdateRequestState(r, newRequestState)
  /\ UNCHANGED <<StateForCacheInvalidator, InvalidationTopicsForVersion, StateForTopicVersionCacheInstance, StateForDataCacheInstance, StateForDatabase>>

HandleDatabaseResponse(r, dc) == 
  LET requestState == StateForRequest[r] IN 
  /\ requestState.type = DatabaseRespondedType
  /\ LET newRequestState == CompletedRequestState(requestState, requestState.databaseResponse) IN
     UpdateRequestState(r, newRequestState)
  /\ IF requestState.maybeCacheVersion = NoneVal THEN
       UNCHANGED StateForDataCacheInstance
     ELSE
       LET dataCacheState == StateForDataCacheInstance[dc] IN
       LET newDataCacheState == 
         UpdateDataCacheForRequest(dataCacheState, requestState.key, requestState.databaseResponse, requestState.maybeCacheVersion.value) IN
       UpdateDataCacheState(dc, newDataCacheState)
  /\ UNCHANGED <<StateForCacheInvalidator, InvalidationTopicsForVersion, StateForTopicVersionCacheInstance, StateForDatabase>>
  
InvalidateCache(ci, tvc) == 
  LET cacheInvalidatorVersion == StateForCacheInvalidator[ci] IN
  LET maybeTopicsForVersion == InvalidationTopicsForVersion[cacheInvalidatorVersion] IN
  /\ maybeTopicsForVersion /= NoneVal
  /\ LET tvcState == StateForTopicVersionCacheInstance[tvc] IN
     LET tvcStateWithUpdatedVersion == UpdatedCacheVersion(tvcState, cacheInvalidatorVersion) IN
     LET updatedCacheVersion == tvcStateWithUpdatedVersion.maybeVersion.value IN
     LET newCacheInvalidatorVersion == updatedCacheVersion + 1 IN
     /\ (IF newCacheInvalidatorVersion \leq MaximumVersion(Version) THEN
          UpdateCacheInvalidatorState(ci, newCacheInvalidatorVersion)
        ELSE
          UNCHANGED StateForCacheInvalidator)
     /\ (IF updatedCacheVersion = cacheInvalidatorVersion THEN
          UpdateTopicVersionCacheState(tvc, InvalidateTopics(tvcStateWithUpdatedVersion, maybeTopicsForVersion.value))
        ELSE 
          UNCHANGED StateForTopicVersionCacheInstance)
  /\ UNCHANGED <<StateForRequest, InvalidationTopicsForVersion, StateForDataCacheInstance, StateForDatabase>>

WriteToDatabase(key) ==
  LET databaseVersion == StateForDatabase.version IN
  LET newDatabaseVersion == databaseVersion + 1 IN
  /\ newDatabaseVersion \leq MaximumVersion(Version)
  /\ LET newDatabaseState == UpdatedDatabaseState(StateForDatabase, key) IN
     /\ UpdateDatabaseState(newDatabaseState)
     /\ LET topicsForKey == TopicsForKey[key] IN
        LET intersectingTopicSets == {ts \in SUBSET Topic: ts \cap topicsForKey /= {}} IN
        \E generatedTopics \in intersectingTopicSets: 
          InvalidationTopicsForVersion' = [InvalidationTopicsForVersion EXCEPT ![newDatabaseVersion] = SomeVal(generatedTopics)]
  /\ UNCHANGED <<StateForRequest, StateForCacheInvalidator, StateForTopicVersionCacheInstance, StateForDataCacheInstance>>

Init ==
  /\ StateForRequest = [r \in Request |-> IdleRequestState]
  /\ StateForCacheInvalidator = [ci \in CacheInvalidator |-> 0]
  /\ InvalidationTopicsForVersion = [[v \in Version |-> NoneVal] EXCEPT ![0] = SomeVal({})]
  /\ StateForTopicVersionCacheInstance = [tvc \in TopicVersionCacheInstance |-> InitialTopicVersionCacheState] 
  /\ StateForDataCacheInstance = [dc \in DataCacheInstance |-> InitialDataCacheState]
  /\ StateForDatabase = InitialDatabaseState

Next == 
  \/ \E r \in Request: \/ \E key \in Key, requestVersion \in {v \in Version: v \leq StateForDatabase.version}: StartRequest(r, key, requestVersion)
                       \/ RequestCaches(r)
                       \/ \E tvc \in TopicVersionCacheInstance: HandleTopicVersionCacheRequest(r, tvc)
                       \/ \E dc \in DataCacheInstance: HandleDataCacheRequest(r, dc)
                       \/ HandleCacheResponses(r)
                       \/ HandleDatabaseRequest(r)
                       \/ \E dc \in DataCacheInstance: HandleDatabaseResponse(r, dc)
  \/ \E ci \in CacheInvalidator, tvc \in TopicVersionCacheInstance: InvalidateCache(ci, tvc)
  \/ \E key \in Key: WriteToDatabase(key)

TypeInvariant == 
  /\ StateForRequest \in [Request -> RequestState]
  /\ StateForCacheInvalidator \in [CacheInvalidator -> Version]
  /\ InvalidationTopicsForVersion \in [Version -> Maybe(SUBSET Topic)]
  /\ StateForTopicVersionCacheInstance \in [TopicVersionCacheInstance -> TopicVersionCacheState]
  /\ StateForDataCacheInstance \in [DataCacheInstance -> DataCacheState]
  /\ StateForDatabase \in DatabaseState

SafetyInvariant == 
  \A r \in Request: LET requestState == StateForRequest[r] IN
                    requestState.type = CompletedType => 
                      LET requestVersion == requestState.requestVersion IN
                      LET responseVersion == requestState.response.lastUpdateVersion IN
                      LET databaseVersion == StateForDatabase.maybeSnapshotForVersion[requestVersion].value[requestState.key].lastUpdateVersion IN
                      databaseVersion \leq responseVersion
==================================================================================
