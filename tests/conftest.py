"""Shared, session-scoped results of the expensive checks, so a report several tests read is computed
once per session. Each fixture returns what the uncached call would; callers get their own copy."""
import copy
import json

import pytest

from physverify.schemes import check


@pytest.fixture(scope="session")
def checked():
    """check(spec, *grids), memoized on its arguments for the session (a deep copy per call, so one
    test cannot change what another sees)."""
    cache = {}

    def run(spec, *args):
        key = json.dumps([spec, args], sort_keys=True, default=repr)
        if key not in cache:
            cache[key] = check(spec, *args)
        return copy.deepcopy(cache[key])
    return run
