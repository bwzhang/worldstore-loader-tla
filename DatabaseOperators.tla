----------------------------- MODULE DatabaseOperators ----------------------------
EXTENDS Types

GetDatabaseResponse(databaseState, key) == databaseState.maybeSnapshotForVersion[databaseState.version].value[key]

UpdatedDatabaseState(databaseState, key) == 
  LET maybeSnapshotForVersion == databaseState.maybeSnapshotForVersion IN
  LET snapshot == maybeSnapshotForVersion[databaseState.version].value IN
  LET newVersion == databaseState.version + 1 IN
  LET newSnapshot == [snapshot EXCEPT ![key] = [lastUpdateVersion |-> newVersion]] IN
  LET newMaybeSnapshotForVersion == [maybeSnapshotForVersion EXCEPT ![newVersion] = SomeVal(newSnapshot)] IN
  [maybeSnapshotForVersion |-> newMaybeSnapshotForVersion, version |-> newVersion]

InitialDatabaseState == 
  LET InitialMaybeSnapshotForVersion == [v \in Version |-> IF v = 0 THEN SomeVal([key \in Key |-> [lastUpdateVersion |-> 0]]) ELSE NoneVal] IN
  [maybeSnapshotForVersion |-> InitialMaybeSnapshotForVersion, version |-> 0]
==================================================================================
