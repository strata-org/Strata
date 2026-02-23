
# How to read expected outputs
`StrataTest/Languages/Python/expected/test_precondition_verification.expected` looks like this:

```
datetime_now_ensures_0: ✅ pass

datetime_utcnow_ensures_0: ✅ pass

ensures_str_strp_reverse: ✅ pass

assert_name_is_foo: ✅ pass

assert_opt_name_none_or_str: ✅ pass

assert_opt_name_none_or_bar: ✅ pass

ensures_maybe_except_none: ✅ pass

test_helper_procedure_assert_name_is_foo_27: ✅ pass

test_helper_procedure_assert_opt_name_none_or_str_28: ✅ pass

test_helper_procedure_assert_opt_name_none_or_bar_29: ✅ pass

test_helper_procedure_assert_name_is_foo_19: ✅ pass

test_helper_procedure_assert_opt_name_none_or_str_20: ✅ pass

test_helper_procedure_assert_opt_name_none_or_bar_21: ✅ pass

test_helper_procedure_assert_name_is_foo_11: failed
CEx: 

test_helper_procedure_assert_opt_name_none_or_str_12: ✅ pass

test_helper_procedure_assert_opt_name_none_or_bar_13: ✅ pass

test_helper_procedure_assert_name_is_foo_3: ✅ pass

test_helper_procedure_assert_opt_name_none_or_str_4: ✅ pass

test_helper_procedure_assert_opt_name_none_or_bar_5: failed
CEx: 
```

This can be read as:

```
assert_name_is_foo: ✅ pass

assert_opt_name_none_or_str: ✅ pass

assert_opt_name_none_or_bar: ✅ pass

ensures_maybe_except_none: ✅ pass
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
test_helper_procedure_assert_name_is_foo_3: ✅ pass

test_helper_procedure_assert_opt_name_none_or_str_4: ✅ pass

test_helper_procedure_assert_opt_name_none_or_bar_5: ❌ fail
```

Comes from checking the assertions in the inlined calls of `test_helper_procedure`. The first two triples succeed, the third has a failure because `"Foo" != "foo"`, and the final has a failure because `"Bar" != "bar"`.
