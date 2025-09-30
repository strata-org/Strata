let day: number = 0;
let result: string = "initial";

switch (day) {
  case 0:
    result = "Sunday";
  case 6:
    result = "Saturday";
    break;
  default:
    result = "Not weekend";
}