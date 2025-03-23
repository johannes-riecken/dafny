// Assuming T is the type of the elements in the array and K is the type of the keys
// The keyGen function should be defined elsewhere in the program

method keyGen<T, K(0)>(element: T) returns (res: K)
{
    return *;
}

method withPositionsOfInInterval<T, K(0)>(aCollection: array<T>, start: nat, end: nat) returns (d: map<K, seq<nat>>)
    requires start <= end && end < aCollection.Length
{
    d := map[];
    var index := start;

    while index <= end
    {
        var element := aCollection[index];
        var key := keyGen(element);
        
        if key in d
        {
            d := d[key := [index] + d[key]]; // Prepend the index to the existing sequence
        }
        else
        {
            d := d[key := [index]]; // Start a new sequence with this index
        }
        index := index + 1;
    }

    return d;
}

datatype Option<T> = None | Some(T)

method ReplaceNextLargerWith(a: seq<int>, aValue: int, high: nat) returns (insertionPoint: Option<int>)
    requires high < |a|
    /* requires a != null && |a| > 0 */
    /* requires high < |a| && high >= -1 */
    /* ensures insertionPoint == null || (0 <= insertionPoint < |a|) */
{
    var ret := a;
    assert high < |ret|;
    if high == -1 || aValue > ret[|ret| - 1] {
        // Append to the end
        ret := ret + [aValue];
        return Some(|ret| - 1);
    }

    var low := 0;
    var index := 0;
    var found: int;
    var j := high;

    while low <= j
    invariant low <= index <= high
    {
        index := (j + low) / 2;
        /* assert index >= 0; */
        /* assert index <= j; */
        /* assert low <= high; */
        /* assert j <= high; */
        /* found := ret[index]; */

        /* if aValue == found { */
        /*     return None; // Value already exists */
        /* } else if aValue > found { */
        /*     low := index + 1; */
        /* } else { */
        /*     j := index - 1; */
        /* } */
    }

    /* // Insertion point is now at `low` */
    /* if low < |ret| { */
    /*     ret[low] := aValue; // Overwrite the next larger value */
    /* } else { */
    /*     ret := ret + [aValue]; // Append to the end */
    /* } */
    
    /* return Some(low); */
}

