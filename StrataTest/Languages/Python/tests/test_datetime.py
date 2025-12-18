from datetime import datetime, date, timedelta

# def my_f(start: datetime, end: datetime):
#     assert start <= end

# def my_f_str(start: str, end : str):
#     format_string : str = "%Y-%m-%d"
#     start_dt : datetime = datetime.strptime(start, format_string)
#     end_dt : datetime = datetime.strptime(end, format_string)
#     assert start_dt <= end_dt

now : datetime = datetime.now()
end : datetime = datetime.date(now)
delta : timedelta = timedelta(days=7)
start : datetime = end - delta

# my_f(start, end)

# my_f_str(str(start), str(end))

assert start <= end, "start_leq_end"

# These require mbqi / autoconfig
start_dt : datetime = datetime.strptime(str(start), "%Y-%m-%d")
assert start_dt == start, "start_dt_eq_start"
end_dt : datetime = datetime.strptime(str(end), "%Y-%m-%d")
assert end_dt == end, "end_dt_eq_end"

# This is unknown
assert start_dt <= end_dt, "start_dt_leq_end_dt"
