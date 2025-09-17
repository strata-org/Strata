function getWeekendName(date: number): string | undefined {
  switch (date) {
    case 0:
      return "Sunday";
    case 6:
      return "Saturday";
  }
}

let day: number = 6;
let weekendName: string | undefined = getWeekendName(day);
