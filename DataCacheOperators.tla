----------------------------- MODULE DataCacheOperators ----------------------------
EXTENDS Types

GetDataCacheResponse(dcState, key) == dcState[key]

UpdateDataCacheForRequest(dcState, key, data, version) == [dcState EXCEPT ![key] = SomeVal([data |-> data, version |-> version])]

InitialDataCacheState == [key \in Key |-> NoneVal]
==================================================================================
