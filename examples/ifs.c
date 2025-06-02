if (meeting == 1 && coffee == 1) {
  energy = energy + 1;
} else {
  energy = energy;
}

if (meeting == 1 && coffee == 0) {
  energy = energy - 2;
} else {
  energy = energy;
}

if (deadline == 1 && coffee == 0) {
  energy = energy - 1;
} else {
  energy = energy;
}

if (deadline == 1 && coffee == 1) {
  energy = energy + 2;
} else {
  energy = energy;
}
