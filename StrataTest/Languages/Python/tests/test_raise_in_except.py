# Test: raise statement inside except block
# Regression test for: raise statement translated as hole causing 'could not infer type'

class C:
    pass

def raise_in_except() -> str:
    try:
        c: C = C()
        return ""
    except Exception as e:
        raise Exception(f'Failed: {e}')

raise_in_except()
