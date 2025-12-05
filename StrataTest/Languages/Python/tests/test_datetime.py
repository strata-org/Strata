from datetime import datetime, date, timedelta

format_string : str = '%Y-%m-%d'

# def my_f(start: datetime, end: datetime):
#     assert start <= end

# def my_f_str(start: str, end : str):
#     assert datetime.strptime(start, format_string) <= datetime.strptime(end, format_string)

now : datetime = datetime.now()
end : datetime = datetime.date(now)
delta : timedelta = timedelta(days=7)
start : datetime = end - delta

assert start <= end

# my_f(start, end)

# my_f_str(str(start), str(end))