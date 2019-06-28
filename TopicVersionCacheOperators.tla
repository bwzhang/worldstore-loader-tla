----------------------------- MODULE TopicVersionCacheOperators ----------------------------
EXTENDS Types

UpdatedTopicVersionCacheForRequest(tvcState, topics) == 
  LET maybeTvcVersion == tvcState.maybeVersion IN
  IF maybeTvcVersion = NoneVal THEN tvcState ELSE 
    LET maybeVersionForTopicWithDefault == [t \in Topic |-> IF tvcState.maybeVersionForTopic[t] = NoneVal THEN maybeTvcVersion ELSE tvcState.maybeVersionForTopic[t]] IN
    LET newMaybeVersionForTopic == [t \in Topic |-> IF t \in topics THEN maybeVersionForTopicWithDefault[t] ELSE tvcState.maybeVersionForTopic[t]] IN
    [tvcState EXCEPT !.maybeVersionForTopic = newMaybeVersionForTopic]

GetTopicVersionCacheResponse(tvcState, topics) ==
  LET topicVersions == {tvcState.maybeVersionForTopic[t].value: t \in topics} IN
  LET maybeTvcVersion == tvcState.maybeVersion IN
  IF maybeTvcVersion = NoneVal THEN NoneVal ELSE 
    SomeVal([maxTopicVersion |-> MaximumVersion(topicVersions), cacheVersion |-> maybeTvcVersion.value])
    
InvalidateTopics(tvcState, topics) ==
  LET maybeVersionForTopic == tvcState.maybeVersionForTopic IN
  LET newmaybeVersionForTopic == [t \in Topic |-> IF t \in topics THEN NoneVal ELSE maybeVersionForTopic[t]] IN
  [tvcState EXCEPT !.maybeVersionForTopic = newmaybeVersionForTopic]

UpdatedCacheVersion(tvcState, newVersion) ==
  LET maybeTvcVersion == tvcState.maybeVersion IN
  LET updatedState == [tvcState EXCEPT !.maybeVersion = SomeVal(newVersion)] IN
  IF maybeTvcVersion = NoneVal THEN updatedState ELSE 
    LET tvcVersion == maybeTvcVersion.value IN
    \* We guarantee that versions are at least 0
    IF tvcVersion = newVersion - 1 THEN updatedState ELSE tvcState

InitialTopicVersionCacheState == [maybeVersionForTopic |-> [t \in Topic |-> NoneVal], maybeVersion |-> NoneVal]
==================================================================================
