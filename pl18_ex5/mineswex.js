var SZ = 12;
var board = [];
for (var r = 0; r < SZ; r++) {
    board[r] = [];
    for (var c = 0; c < SZ; c++) {
        board[r][c] = Math.random() < 0.08 ? 1 : 0;
    }
}


function around(row, col)
{
    var acc = colwise(row);
    function colwise(row) {
        var acc = 0;
        if (col > 0) acc += board[row][col-1];
        if (col < SZ-1) acc += board[row][col+1];
        return acc;
    }
    if (row > 0) {
        acc += board[row-1][col] + colwise(row-1);
    }
    if (row < SZ-1) {
        acc += board[row+1][col] + colwise(row+1);
    }
    return acc;
}


/**
 * Returns the cell element at (row, col).
 * @param row - row index, zero-based
 * @param col - column index, zero-based
 */
function get_cell(row, col)
{
    return $('div').eq(row * SZ + col);
}


/**
 * Returns true if the given cell object has not yet
 * been revealed.
 */
function is_cell_hidden(cellobj)
{
    return cellobj.is(":hidden");
}

function nxt() {
    var i = $('div').index($(this));
    var row = Math.floor(i / SZ);
    var col = i % SZ;
    var value = around(row, col);
    if (board[row][col]) {
        $(this).addClass("mine");
    } else {
        $(this).text(value);
        /* ADD YOUR CODE HERE */
        if(value == 0){
            revealZeroCells(row, col);
        }
        
    }
}

function revealZeroCells(row, col){
    $(get_cell(row, col)).fadeIn();
    for(var i = row -1; i <= row + 1;i++){
        for(var j = col -1; j <= col + 1;j++){
            if(i >= 0 && j >=0 && i < SZ && j < SZ && !(i == row && j == col)){
                var cell = get_cell(i, j);
                if(is_cell_hidden(cell)){
                    $(cell).fadeIn(nxt);
                }
            }
        }
    }
}

$(function() {
    $('td').append('<div/>');
    $('td').mousedown(function() { $(this).find("div").fadeIn(nxt); });
});


