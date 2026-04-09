import servicelib

# Regression test for evalIfCanonical (Issue #812).
# The bucket parameter is symbolic.  The pyspec regex precondition
# re_search_bool("^[a-z0-9-]+$", bucket) has a constant pattern (arg 0)
# but a symbolic string (arg 1).  Without evalIfCanonical, concreteEval
# never fires and the regex stays uninterpreted, making the precondition
# unprovable.  With evalIfCanonical 0, the pattern compiles to an SMT
# regex and the solver uses the path condition to verify the match.

def store_with_symbolic_bucket(bucket: str) -> bool:
    if bucket == "my-bucket":
        client = servicelib.connect("storage")
        client.put_item(Bucket=bucket, Key="mykey", Data="hello")
    return True
