
# How to read expected outputs
`StrataTest/Languages/Python/expected/test_precondition_verification.expected` looks like this:

```
assert_name_is_foo: verified

assert_opt_name_none_or_str: verified

assert_opt_name_none_or_bar: verified

ensures_maybe_except_none: verified

test_helper_procedure_assert_name_is_foo_3: verified

test_helper_procedure_assert_opt_name_none_or_str_4: verified

test_helper_procedure_assert_opt_name_none_or_bar_5: verified

test_helper_procedure_assert_name_is_foo_11: verified

test_helper_procedure_assert_opt_name_none_or_str_12: verified

test_helper_procedure_assert_opt_name_none_or_bar_13: verified

test_helper_procedure_assert_name_is_foo_19: failed
CEx: 

test_helper_procedure_assert_opt_name_none_or_str_20: verified

test_helper_procedure_assert_opt_name_none_or_bar_21: verified

test_helper_procedure_assert_name_is_foo_27: verified

test_helper_procedure_assert_opt_name_none_or_str_28: verified

test_helper_procedure_assert_opt_name_none_or_bar_29: unknown

```

This can be read as:

```
assert_name_is_foo: verified

assert_opt_name_none_or_str: verified

assert_opt_name_none_or_bar: verified

ensures_maybe_except_none: verified
```

These come from checking that the assertions/ensures in `test_helper_procedure` hold.
```
procedure test_helper_procedure(req_name : string, opt_name : StrOrNone) returns (maybe_except: ExceptOrNone)
spec {
  requires [req_name_is_foo]: req_name == "foo";
  requires [req_opt_name_none_or_str]: (if (StrOrNone_tag(opt_name) != SN_NONE_TAG) then (StrOrNone_tag(opt_name) == SN_STR_TAG) else true);
  requires [req_opt_name_none_or_bar]: (if (StrOrNone_tag(opt_name) == SN_STR_TAG) then (StrOrNone_str_val(opt_name) == "bar") else true);
  ensures [ensures_maybe_except_none]: (ExceptOrNone_tag(maybe_except) == EN_NONE_TAG);
}
{
  assert [assert_name_is_foo]: req_name == "foo";
  assert [assert_opt_name_none_or_str]: (if (StrOrNone_tag(opt_name) != SN_NONE_TAG) then (StrOrNone_tag(opt_name) == SN_STR_TAG) else true);
  assert [assert_opt_name_none_or_bar]: (if (StrOrNone_tag(opt_name) == SN_STR_TAG) then (StrOrNone_str_val(opt_name) == "bar") else true);
  assume [assume_maybe_except_none]: (ExceptOrNone_tag(maybe_except) == EN_NONE_TAG);
};
```

Each of the following triples:
```
test_helper_procedure_assert_name_is_foo_3: verified

test_helper_procedure_assert_opt_name_none_or_str_5: verified

test_helper_procedure_assert_opt_name_none_or_bar_5: verified
```

Comes from checking the assertions in the inlined calls of `test_helper_procedure`. The first two triples succeed, the third has a failure because `"Foo" != "foo"` and the final has an `unknown` (that should ideally be a failure) because `"Bar" != "bar"`.