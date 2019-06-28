----------------------------- MODULE RequestOperators ----------------------------
EXTENDS Types

IdleRequestState == [type |-> IdleType]

StartedRequestState(key, requestVersion) ==
  [
    type |-> StartedType, 
    key |-> key, 
    requestVersion |-> requestVersion
  ]

CachesRequestedRequestState(requestState) ==
  [
    type |-> CachesRequestedType, 
    key |-> requestState.key, 
    requestVersion |-> requestState.requestVersion, 
    maybeTopicVersionCacheResponse |-> NoneVal,
    maybeDataCacheResponse |-> NoneVal
  ]

CacheMissRequestState(requestState, maybeCacheVersion) ==
  [
    type |-> CacheMissType,
    key |-> requestState.key,
    requestVersion |-> requestState.requestVersion,
    maybeCacheVersion |-> maybeCacheVersion
  ]

DatabaseRespondedRequestState(requestState, databaseResponse) ==
  [
    type |-> DatabaseRespondedType,
    key |-> requestState.key,
    requestVersion |-> requestState.requestVersion,
    maybeCacheVersion |-> requestState.maybeCacheVersion,
    databaseResponse |-> databaseResponse
  ]

CompletedRequestState(requestState, response) ==
  [
    type |-> CompletedType,
    key |-> requestState.key,
    requestVersion |-> requestState.requestVersion,
    response |-> response
  ]
==================================================================================
