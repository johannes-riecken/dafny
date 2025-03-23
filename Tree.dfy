method longest(lines: seq<string>) returns (maxLen: nat)
requires |lines| > 0
ensures forall i | 0 <= i < |lines| :: |lines[i]| <= maxLen
ensures exists i | 0 <= i < |lines| :: |lines[i]| == maxLen
{
  maxLen := |lines[0]|;
  var i := 1;
  while i < |lines|
  invariant 1 <= i <= |lines|
  invariant forall j | 0 <= j < i :: |lines[j]| <= maxLen
  invariant exists j | 0 <= j < i :: |lines[j]| == maxLen
  {
    var line := lines[i];
    if |line| > maxLen {
      maxLen := |line|;
    }
    i := i + 1;
  }
}

method pad(lines: seq<string>, width: nat) returns (paddedLines: seq<string>)
requires |lines| > 0
{
    var actualWidth := width;
    if width <= 0 {
        actualWidth := longest(lines);
    }
    paddedLines := [];
    var i := 0;
    while i < |lines|
    {
        var line := lines[i];
        var padLength := actualWidth - |line|;
        var padding := "";
        if (padLength > 0) {
            padding := seq(padLength, _ => ' '); // Create a string of spaces
        }
        paddedLines := paddedLines + [line + padding];
        i := i + 1;
    }
}

