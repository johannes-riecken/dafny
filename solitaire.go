package main
const N = 11 + 1 // length of a board row (+1 for newline)
var board = []rune(
	`...........
...........
....●●●....
....●●●....
..●●●●●●●..
..●●●○●●●..
..●●●●●●●..
....●●●....
....●●●....
...........
...........
`)
var center int
func init() {
	n := 0
	for pos, field := range board {
		if field == '○' {
			center = pos
			n++
		}
	}
	if n != 1 {
		center = -1 // no single hole
	}
}
var moves int // number of times move is called
func move(pos, dir int) bool {
	moves++
	if board[pos] == '●' && board[pos+dir] == '●' && board[pos+2*dir] == '○' {
		board[pos] = '○'
		board[pos+dir] = '○'
		board[pos+2*dir] = '●'
		return true
	}
	return false
}
func unmove(pos, dir int) {
	board[pos] = '●'
	board[pos+dir] = '●'
	board[pos+2*dir] = '○'
}
func solve() bool {
	var last, n int
	for pos, field := range board {
		// try each board position
		if field == '●' {
			// found a peg
			for _, dir := range [...]int{-1, -N, +1, +N} {
				// try each direction
				if move(pos, dir) {
					// a valid move was found and executed,
					// see if this new board has a solution
					if solve() {
						unmove(pos, dir)
						println(string(board))
						return true
					}
					unmove(pos, dir)
				}
			}
			last = pos
			n++
		}
	}
	// tried each possible move
	if n == 1 && (center < 0 || last == center) {
		// there's only one peg left
		println(string(board))
		return true
	}
	// no solution found for this board
	return false
}
func main() {
	if !solve() {
		println("no solution found")
	}
	println(moves, "moves tried")
}
