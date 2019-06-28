----------------------------- MODULE Types ----------------------------
EXTENDS Integers

CONSTANT Request,
         Version,
         Key,
         Topic,
         TopicsForKey,
         TopicVersionCacheInstance,
         DataCacheInstance,
         CacheInvalidator

ASSUME
  /\ Version \subseteq Nat
  /\ \A v \in Version: v \geq 0
  /\ (\A v \in Version: v = 0 \/ (v - 1) \in Version)

ASSUME 
  /\ TopicsForKey \in [Key -> SUBSET Topic]
  /\ \A k \in Key: TopicsForKey[k] /= {}

\* We pretend the data contains the version associated with its latest 
\* update. This is only used by the safety invariant.
Data == [lastUpdateVersion: Version]

NoneVal == [type |-> "None"]
SomeVal(value) == [type |-> "Some", value |-> value]
Maybe(valueSet) == [type: {"None"}] \cup [type: {"Some"}, value: valueSet]

TopicVersionCacheResponse == Maybe([maxTopicVersion: Version, cacheVersion: Version])
TopicVersionCacheState == [maybeVersionForTopic: [Topic -> Maybe(Version)], maybeVersion: Maybe(Version)]

DataCacheResponse == Maybe([data: Data, version: Version])
DataCacheState == [Key -> DataCacheResponse]

DatabaseResponse == Data
DatabaseSnapshot == [Key -> DatabaseResponse]
DatabaseState == [maybeSnapshotForVersion: [Version -> Maybe(DatabaseSnapshot)], version: Version]

IdleType == "Idle"
StartedType == "Started"
CachesRequestedType == "CachesRequested"
CacheMissType == "CacheMiss"
DatabaseRespondedType == "DatabaseResponded"
CompletedType == "Complete"

RequestState ==
  [type: {IdleType}]
      \cup
  [
    type: {StartedType}, 
    key: Key, 
    requestVersion: Version
  ]
      \cup
  [
    type: {CachesRequestedType}, 
    key: Key, 
    requestVersion: Version, 
    maybeTopicVersionCacheResponse: Maybe(TopicVersionCacheResponse), 
    maybeDataCacheResponse: Maybe(DataCacheResponse)
  ]
      \cup
  [
    type: {CacheMissType}, 
    key: Key, 
    requestVersion: Version, 
    maybeCacheVersion: Maybe(Version)
  ]
      \cup
  [
    type: {DatabaseRespondedType}, 
    key: Key, 
    requestVersion: Version, 
    maybeCacheVersion: Maybe(Version), 
    databaseResponse: DatabaseResponse
  ]
      \cup
  [type: {CompletedType}, key: Key, requestVersion: Version, response: Data]

MaximumVersion(versions) == 
  IF versions = {} THEN -1 ELSE CHOOSE n \in versions : \A m \in versions : n \geq m
==================================================================================
