/* ================================
GLOBAL STATE
================================ */
let currentPuzzle = null;
let size = 6;
let gridData = [];
let solutionPath = [];
let path = [];
let currentNumber = 1;
let timer = 0;
let interval = null;
let isMouseDown = false;
let hintActive = false;
let gameOver = false;
let gamesPlayed = 0;
let zipNumber = 1;
let lastTouchCell = null;

// Walls arrays
let hWalls = [];
let vWalls = [];

/* ================================
CANVAS
================================ */
let canvas = document.getElementById("pathCanvas");
let ctx = canvas.getContext("2d");

/* ================================
INFO MODAL
================================ */
function openInfo() {
  const modal = document.getElementById("infoModal");
  if (modal) modal.style.display = "flex";
}
function closeInfo() {
  const modal = document.getElementById("infoModal");
  if (modal) modal.style.display = "none";
}
window.addEventListener("click", function (e) {
  const modal = document.getElementById("infoModal");
  if (e.target === modal) {
    modal.style.display = "none";
  }
});

/* ================================
SHUFFLE
================================ */
function shuffle(arr) {
  for (let i = arr.length - 1; i > 0; i--) {
    let j = Math.floor(Math.random() * (i + 1));
    [arr[i], arr[j]] = [arr[j], arr[i]];
  }
}

/* ================================
HAMILTONIAN PATH GENERATION (Warnsdorff)
================================ */
function generateHamiltonianPath(size) {
  const dirs = [[1, 0], [-1, 0], [0, 1], [0, -1]];
  const visited = Array(size).fill().map(() => Array(size).fill(false));
  const path = [];

  let r = Math.floor(Math.random() * size);
  let c = Math.floor(Math.random() * size);

  function countUnvisitedNeighbors(r, c) {
    let count = 0;
    for (let [dr, dc] of dirs) {
      let nr = r + dr, nc = c + dc;
      if (nr >= 0 && nr < size && nc >= 0 && nc < size && !visited[nr][nc]) count++;
    }
    return count;
  }

  function dfs(r, c) {
    visited[r][c] = true;
    path.push({ r, c });

    if (path.length === size * size) return true;

    const neighbors = [];
    for (let [dr, dc] of dirs) {
      let nr = r + dr, nc = c + dc;
      if (nr >= 0 && nr < size && nc >= 0 && nc < size && !visited[nr][nc]) {
        neighbors.push({ nr, nc, count: countUnvisitedNeighbors(nr, nc) });
      }
    }
    neighbors.sort((a, b) => a.count - b.count);

    for (let { nr, nc } of neighbors) {
      if (dfs(nr, nc)) return true;
    }

    visited[r][c] = false;
    path.pop();
    return false;
  }

  dfs(r, c);
  return path;
}

/* ================================
EFFICIENT SOLUTION COUNTER (with safety checks)
================================ */
function countSolutions(grid, size) {
  const maxNum = getMaxNumber(grid);
  const totalCells = size * size;
  const dirs = [[1, 0], [-1, 0], [0, 1], [0, -1]];

  let startR = -1, startC = -1;
  for (let r = 0; r < size; r++) {
    for (let c = 0; c < size; c++) {
      if (grid[r][c] === 1) {
        startR = r; startC = c;
        break;
      }
    }
  }
  if (startR === -1) return 0;

  const cellIndex = (r, c) => {
    if (typeof r !== 'number' || typeof c !== 'number' || isNaN(r) || isNaN(c)) return 0;
    return r * size + c;
  };
  const manhattan = (r1, c1, r2, c2) => Math.abs(r1 - r2) + Math.abs(c1 - c2);

  function isRemainingConnected(visitedMask, excludeCell) {
    let first = -1;
    for (let i = 0; i < totalCells; i++) {
      if (typeof i !== 'number' || isNaN(i)) continue;
      if (!(visitedMask & (1n << BigInt(i))) && i !== excludeCell) {
        first = i;
        break;
      }
    }
    if (first === -1) return true;

    let queue = [first];
    let seen = 1n << BigInt(first);
    while (queue.length) {
      let idx = queue.shift();
      let r = Math.floor(idx / size);
      let c = idx % size;
      for (let [dr, dc] of dirs) {
        let nr = r + dr, nc = c + dc;
        if (nr < 0 || nr >= size || nc < 0 || nc >= size) continue;
        let nidx = nr * size + nc;
        if (nidx === excludeCell) continue;
        if (!(visitedMask & (1n << BigInt(nidx))) && !(seen & (1n << BigInt(nidx)))) {
          seen |= 1n << BigInt(nidx);
          queue.push(nidx);
        }
      }
    }
    for (let i = 0; i < totalCells; i++) {
      if (i === excludeCell) continue;
      if (!(visitedMask & (1n << BigInt(i))) && !(seen & (1n << BigInt(i)))) {
        return false;
      }
    }
    return true;
  }

  let solutions = 0;

  function dfs(r, c, visitedMask, nextNum, steps) {
    if (typeof r !== 'number' || typeof c !== 'number' || isNaN(r) || isNaN(c)) return;

    if (grid[r][c] !== 0 && grid[r][c] !== nextNum) return;
    if (grid[r][c] === nextNum) nextNum++;

    let idx = cellIndex(r, c);
    visitedMask |= 1n << BigInt(idx);
    steps++;

    if (steps === totalCells) {
      if (nextNum > maxNum) solutions++;
      return;
    }

    if (nextNum <= maxNum) {
      let targetR = -1, targetC = -1;
      for (let rr = 0; rr < size; rr++) {
        for (let cc = 0; cc < size; cc++) {
          if (grid[rr][cc] === nextNum) {
            targetR = rr; targetC = cc;
            break;
          }
        }
      }
      if (targetR !== -1) {
        if (manhattan(r, c, targetR, targetC) > totalCells - steps) return;
        if (visitedMask & (1n << BigInt(cellIndex(targetR, targetC)))) return;
      }
    }

    if (!isRemainingConnected(visitedMask, idx)) return;

    const neighbors = [];
    for (let [dr, dc] of dirs) {
      let nr = r + dr, nc = c + dc;
      if (nr < 0 || nr >= size || nc < 0 || nc >= size) continue;
      if (visitedMask & (1n << BigInt(cellIndex(nr, nc)))) continue;
      neighbors.push({ nr, nc });
    }

    if (nextNum <= maxNum) {
      let targetR = -1, targetC = -1;
      for (let rr = 0; rr < size; rr++) {
        for (let cc = 0; cc < size; cc++) {
          if (grid[rr][cc] === nextNum) {
            targetR = rr; targetC = cc;
            break;
          }
        }
      }
      if (targetR !== -1) {
        neighbors.sort((a, b) =>
          manhattan(a.nr, a.nc, targetR, targetC) - manhattan(b.nr, b.nc, targetR, targetC)
        );
      }
    }

    for (let { nr, nc } of neighbors) {
      dfs(nr, nc, visitedMask, nextNum, steps);
      if (solutions > 1) return;
    }
  }

  dfs(startR, startC, 0n, 1, 0);
  return solutions;
}

function getMaxNumber(grid) {
  let max = 0;
  for (let row of grid) {
    for (let val of row) {
      if (val > max) max = val;
    }
  }
  return max;
}

/* ================================
PUZZLE GENERATOR (with exact clue count)
================================ */
function generateUniquePuzzle(difficulty) {
  const params = {
    "easy": { size: 6, maxNumber: 6, wallRange: [0, 0] },
    "easy+": { size: 6, maxNumber: 8, wallRange: [0, 0] },
    "moderate": { size: 6, maxNumber: 10, wallRange: [0, 0] },
    "moderate+": { size: 7, maxNumber: 12, wallRange: [0, 0] },
    "hard": { size: 7, maxNumber: 14, wallRange: [0, 0] },
    "hard+": { size: 7, maxNumber: 14, wallRange: [5, 12] }
  };

  let { size, maxNumber, wallRange } = params[difficulty];

  // Try up to 200 times to generate a unique puzzle
  for (let attempt = 0; attempt < 200; attempt++) {
    const path = generateHamiltonianPath(size);

    // Choose clue indices: first, last, and random distinct ones in between
    let indices = [0];
    let available = [];
    for (let i = 1; i < path.length - 1; i++) available.push(i);
    shuffle(available);
    for (let i = 0; i < maxNumber - 2; i++) {
      if (i < available.length) indices.push(available[i]);
    }
    indices.push(path.length - 1);
    indices.sort((a, b) => a - b);

    if (indices.length !== maxNumber) continue; // not enough distinct indices

    let grid = Array(size).fill().map(() => Array(size).fill(0));
    for (let i = 0; i < indices.length; i++) {
      let { r, c } = path[indices[i]];
      grid[r][c] = i + 1;
    }

    if (countSolutions(grid, size) === 1) {
      // Add walls if hard+
      let hWalls = Array(size).fill().map(() => Array(size - 1).fill(false));
      let vWalls = Array(size).fill().map(() => Array(size - 1).fill(false));

      if (difficulty === "hard+") {
        let numWalls = Math.floor(Math.random() * (wallRange[1] - wallRange[0] + 1)) + wallRange[0];

        let pathEdges = new Set();
        for (let i = 0; i < path.length - 1; i++) {
          let { r: r1, c: c1 } = path[i];
          let { r: r2, c: c2 } = path[i + 1];
          if (r1 === r2) {
            let cMin = Math.min(c1, c2);
            pathEdges.add(`v:${r1}:${cMin}`);
          } else {
            let rMin = Math.min(r1, r2);
            pathEdges.add(`h:${rMin}:${c1}`);
          }
        }

        let nonPathEdges = [];
        for (let r = 0; r < size - 1; r++) {
          for (let c = 0; c < size; c++) {
            if (!pathEdges.has(`h:${r}:${c}`)) {
              nonPathEdges.push({ type: 'h', r, c });
            }
          }
        }
        for (let r = 0; r < size; r++) {
          for (let c = 0; c < size - 1; c++) {
            if (!pathEdges.has(`v:${r}:${c}`)) {
              nonPathEdges.push({ type: 'v', r, c });
            }
          }
        }

        shuffle(nonPathEdges);
        let selected = nonPathEdges.slice(0, numWalls);
        for (let w of selected) {
          if (w.type === 'h') hWalls[w.r][w.c] = true;
          else vWalls[w.r][w.c] = true;
        }
      }

      return { size, grid, solution: path, hWalls, vWalls };
    }
  }

  // Fallback (very rare) – ensure last number is at the last cell
  console.warn("Using fallback puzzle generation");
  const path = generateHamiltonianPath(size);
  let grid = Array(size).fill().map(() => Array(size).fill(0));

  // Always include first and last indices
  let indices = [0];
  let step = Math.floor((path.length - 1) / (maxNumber - 1));
  for (let i = 1; i < maxNumber - 1; i++) {
    indices.push(Math.min(i * step, path.length - 2));
  }
  indices.push(path.length - 1);
  indices.sort((a, b) => a - b);

  for (let i = 0; i < indices.length; i++) {
    let { r, c } = path[indices[i]];
    grid[r][c] = i + 1;
  }

  return { size, grid, solution: path, hWalls: [], vWalls: [] };
}

/* ================================
DIFFICULTY (extended)
================================ */
function getDifficulty() {
  if (gamesPlayed < 3) return "easy";
  if (gamesPlayed < 6) return "easy+";
  if (gamesPlayed < 10) return "moderate";
  if (gamesPlayed < 15) return "moderate+";
  if (gamesPlayed < 21) return "hard";
  return "hard+";
}

/* ================================
LOAD NEXT PUZZLE (async)
================================ */
function loadNextPuzzle() {
  document.body.style.cursor = 'wait';

  setTimeout(() => {

    let difficulty = getDifficulty();
    let puzzle = generateUniquePuzzle(difficulty);

    currentPuzzle = puzzle;
    size = puzzle.size;
    gridData = puzzle.grid;
    solutionPath = puzzle.solution;
    hWalls = puzzle.hWalls;
    vWalls = puzzle.vWalls;

    path = [];
    currentNumber = 1;
    hintActive = false;
    gameOver = false;

    timer = 0;
    clearInterval(interval);
    interval = null;
    updateTimerDisplay();

    document.getElementById("gameTitle").textContent =
      `Zip #${zipNumber} - ${difficulty}`;

    // ✅ FIXED: apply difficulty class correctly
    const container = document.querySelector(".container");
    container.className = "container " + difficulty.replace("+", "-plus");

    createGrid();

    document.body.style.cursor = 'default';

  }, 0);
}
/* ================================
GRID
================================ */
function createGrid() {
  const gridEl = document.getElementById("grid");
  if (!gridEl) return;
  gridEl.innerHTML = "";
  gridEl.style.gridTemplateColumns = `repeat(${size}, 1fr)`;

  for (let r = 0; r < size; r++) {
    for (let c = 0; c < size; c++) {
      const cell = document.createElement("div");
      cell.classList.add("cell");
      cell.dataset.row = r;
      cell.dataset.col = c;

      let value = gridData[r][c];
      if (value !== 0) {
        cell.textContent = value;
        cell.classList.add("number");
      }

      cell.addEventListener("mousedown", (e) => {
        isMouseDown = true;
        startDrag(e);
      });
      cell.addEventListener("mouseover", (e) => {
        if (isMouseDown) dragOver(e);
      });
      cell.addEventListener("click", handleBacktrack);

      gridEl.appendChild(cell);
    }
  }

  resizeCanvas();
}

document.addEventListener("mouseup", () => {
  isMouseDown = false;
});

document.addEventListener("touchstart", (e) => {
  if (gameOver) return;

  const touch = e.touches[0];
  const element = document.elementFromPoint(touch.clientX, touch.clientY);

  if (!element || !element.classList.contains("cell")) return;

  isMouseDown = true;
  startDrag({ target: element });
});

document.addEventListener("touchmove", (e) => {
  if (!isMouseDown || gameOver) return;

  e.preventDefault();

  const touch = e.touches[0];

  const grid = document.getElementById("grid");
  const rect = grid.getBoundingClientRect();

  const x = touch.clientX - rect.left;
  const y = touch.clientY - rect.top;

  const cellSize = rect.width / size;

  const c = Math.floor(x / cellSize);
  const r = Math.floor(y / cellSize);

  if (r < 0 || r >= size || c < 0 || c >= size) return;

  const current = { r, c };

  // 🔥 SAME CELL → ignore
  if (lastTouchCell && lastTouchCell.r === r && lastTouchCell.c === c) return;

  // 🔥 INTERPOLATION (SMOOTH FILL)
  if (lastTouchCell) {
    let dr = r - lastTouchCell.r;
    let dc = c - lastTouchCell.c;

    let steps = Math.max(Math.abs(dr), Math.abs(dc));

    for (let i = 1; i <= steps; i++) {
      let nr = lastTouchCell.r + Math.round((dr * i) / steps);
      let nc = lastTouchCell.c + Math.round((dc * i) / steps);

      const el = document.querySelector(
        `[data-row='${nr}'][data-col='${nc}']`
      );

      if (el) {
        dragOver({ target: el });
      }
    }
  } else {
    const el = document.querySelector(
      `[data-row='${r}'][data-col='${c}']`
    );
    if (el) dragOver({ target: el });
  }

  lastTouchCell = current;

}, { passive: false });

document.addEventListener("touchend", () => {
  isMouseDown = false;
  lastTouchCell = null;
});

document.body.addEventListener("touchmove", function (e) {
  if (isMouseDown) e.preventDefault();
}, { passive: false });

/* ================================
WALL CHECK
================================ */
function hasWall(r1, c1, r2, c2) {
  if (r1 === r2) {
    let c = Math.min(c1, c2);
    return vWalls[r1]?.[c] === true;
  } else {
    let r = Math.min(r1, r2);
    return hWalls[r]?.[c1] === true;
  }
}

/* ================================
CANVAS (with walls)
================================ */
function resizeCanvas() {
  const grid = document.getElementById("grid");
  if (!grid) return;
  const width = grid.offsetWidth;
  const height = grid.offsetHeight;
  if (width === 0 || height === 0) {
    setTimeout(resizeCanvas, 50);
    return;
  }
  canvas.width = width;
  canvas.height = height;
  redrawCanvas();
}

function getCellCenter(r, c) {
  const cell = document.querySelector(`[data-row='${r}'][data-col='${c}']`);
  if (!cell) return { x: 0, y: 0 };
  const rect = cell.getBoundingClientRect();
  const gridRect = document.getElementById("grid").getBoundingClientRect();
  return {
    x: rect.left - gridRect.left + rect.width / 2,
    y: rect.top - gridRect.top + rect.height / 2
  };
}

function drawPath() {
  if (path.length < 2) return;

  ctx.save();

  ctx.strokeStyle = "#00f0ff";
  ctx.lineWidth = 30;
  ctx.lineCap = "round";
  ctx.lineJoin = "round";
  ctx.shadowColor = "#00f0ff";
  ctx.shadowBlur = 15;

  ctx.beginPath();

  let start = getCellCenter(path[0].r, path[0].c);
  ctx.moveTo(start.x, start.y);

  for (let i = 1; i < path.length - 1; i++) {
    let p1 = getCellCenter(path[i].r, path[i].c);
    let p2 = getCellCenter(path[i + 1].r, path[i + 1].c);

    let midX = (p1.x + p2.x) / 2;
    let midY = (p1.y + p2.y) / 2;

    ctx.quadraticCurveTo(p1.x, p1.y, midX, midY);
  }

  let last = getCellCenter(path[path.length - 1].r, path[path.length - 1].c);
  ctx.lineTo(last.x, last.y);

  ctx.stroke();
  ctx.restore();
}

function drawWalls() {
  if (!hWalls || !vWalls) return;
  const cellW = canvas.width / size;
  const cellH = canvas.height / size;
  ctx.save();
  ctx.strokeStyle = "#333";
  ctx.lineWidth = 4;
  ctx.shadowBlur = 0;

  for (let r = 0; r < size - 1; r++) {
    for (let c = 0; c < size; c++) {
      if (hWalls[r] && hWalls[r][c]) {
        ctx.beginPath();
        ctx.moveTo(c * cellW, (r + 1) * cellH);
        ctx.lineTo((c + 1) * cellW, (r + 1) * cellH);
        ctx.stroke();
      }
    }
  }
  for (let r = 0; r < size; r++) {
    for (let c = 0; c < size - 1; c++) {
      if (vWalls[r] && vWalls[r][c]) {
        ctx.beginPath();
        ctx.moveTo((c + 1) * cellW, r * cellH);
        ctx.lineTo((c + 1) * cellW, (r + 1) * cellH);
        ctx.stroke();
      }
    }
  }
  ctx.restore();
}

function redrawCanvas() {
  requestAnimationFrame(() => {
    ctx.clearRect(0, 0, canvas.width, canvas.height);
    drawWalls();
    drawPath();
  });
}

/* ================================
DRAG / PATH
================================ */
function startDrag(e) {
  if (gameOver) return;
  const cell = e.target;
  const r = +cell.dataset.row;
  const c = +cell.dataset.col;
  const value = gridData[r][c];
  if (path.length === 0 && value !== 1) return;
  if (path.length === 0) startTimer();
  addToPath(cell, r, c, value);
}

function dragOver(e) {
  if (!isMouseDown || gameOver) return;
  const cell = e.target;
  const r = +cell.dataset.row;
  const c = +cell.dataset.col;
  const value = gridData[r][c];
  addToPath(cell, r, c, value);
}

function addToPath(cell, r, c, value) {
  if (!cell || !cell.classList.contains("cell")) return;
  const index = path.findIndex(p => p.r === r && p.c === c);
  if (index !== -1) {
    removePathFrom(index);
    return;
  }

  if (path.length > 0) {
    const last = path[path.length - 1];
    if (Math.abs(last.r - r) + Math.abs(last.c - c) !== 1) return;
    if (hasWall(last.r, last.c, r, c)) return;
  }

  // Allow any blank cell, but numbered cells must be in order
  if (value !== 0 && value !== currentNumber) return;

  path.push({ r, c });
  cell.classList.add("path");
  if (value === currentNumber) currentNumber++;
  redrawCanvas();
  checkWin();
}

function removePathFrom(index) {
  for (let i = path.length - 1; i >= index; i--) {
    const p = path[i];
    const cell = document.querySelector(`[data-row='${p.r}'][data-col='${p.c}']`);
    if (cell) cell.classList.remove("path");
  }
  path = path.slice(0, index);
  currentNumber = 1;
  for (let p of path) {
    let val = gridData[p.r][p.c];
    if (val === currentNumber) currentNumber++;
  }
  redrawCanvas();
}

function handleBacktrack(e) {
  if (gameOver) return;
  const r = Number(e.target.dataset.row);
  const c = Number(e.target.dataset.col);
  const index = path.findIndex(p => p.r === r && p.c === c);
  if (index !== -1) removePathFrom(index);
}

/* ================================
HINT (with arrow)
================================ */
function showHint() {
  if (hintActive || gameOver) return;
  hintActive = true;
  const btn = document.getElementById("hintBtn");
  const fill = document.getElementById("hintFill");
  btn.classList.add("disabled");

  let correctIndex = 0;
  for (let i = 0; i < path.length; i++) {
    if (path[i].r !== solutionPath[i].r || path[i].c !== solutionPath[i].c) break;
    correctIndex++;
  }
  if (correctIndex < path.length) {
    removePathFrom(correctIndex);
  }

  // Hint segment from the last correct cell (correctIndex-1) to the next numbered cell
  let start = Math.max(0, correctIndex - 1);
  let end = start + 1;
  while (end < solutionPath.length && gridData[solutionPath[end].r][solutionPath[end].c] === 0) end++;
  const segment = solutionPath.slice(start, end + 1);
  let duration = 3000;
  let startTime = Date.now();

  function animate() {
    let elapsed = Date.now() - startTime;
    let percent = Math.min(elapsed / duration, 1);

    fill.style.width = (percent * 100, 100) + "%";

    ctx.clearRect(0, 0, canvas.width, canvas.height);
    drawWalls();
    drawPath();

    if (Math.floor(elapsed / 250) % 2 === 0) {
      ctx.save();
      ctx.strokeStyle = "rgba(255,255,0,0.95)";
      ctx.lineWidth = 24;
      ctx.shadowColor = "yellow";
      ctx.shadowBlur = 30;
      ctx.beginPath();
      let s = getCellCenter(segment[0].r, segment[0].c);
      ctx.moveTo(s.x, s.y);
      for (let i = 1; i < segment.length; i++) {
        let p = getCellCenter(segment[i].r, segment[i].c);
        ctx.lineTo(p.x, p.y);
      }
      ctx.stroke();

      // Draw arrowhead at the end of the segment
      if (segment.length >= 2) {
        let last = segment[segment.length - 1];
        let prev = segment[segment.length - 2];
        // Direction from prev to last
        let dx = last.c - prev.c;
        let dy = last.r - prev.r;

        let p1 = getCellCenter(prev.r, prev.c);
        let p2 = getCellCenter(last.r, last.c);

        let angle = Math.atan2(p2.y - p1.y, p2.x - p1.x);

        ctx.save();
        ctx.translate(p2.x, p2.y);
        ctx.rotate(angle);

        ctx.fillStyle = "yellow";
        ctx.shadowColor = "yellow";
        ctx.shadowBlur = 20;

        ctx.beginPath();
        ctx.moveTo(0, 0);
        ctx.lineTo(-15, -8);
        ctx.lineTo(-15, 8);
        ctx.closePath();
        ctx.fill();
        // Optional outline for visibility
        ctx.strokeStyle = "orange";
        ctx.lineWidth = 2;
        ctx.shadowBlur = 0;
        ctx.stroke();
        ctx.restore();
      }
      ctx.restore();
    }

    if (percent < 1) {
      requestAnimationFrame(animate);
    } else {
      fill.style.width = "100%";
      setTimeout(() => {
        hintActive = false;
        btn.classList.remove("disabled");
        fill.style.width = "0%";
        redrawCanvas();
      }, 200);
    }
  }
  animate();
}

/* ================================
TIMER (MM:SS after 60s)
================================ */
function updateTimerDisplay() {
  const el = document.getElementById("timer");
  if (timer < 60) {
    el.textContent = "⏱ " + timer + "s";
  } else {
    let minutes = Math.floor(timer / 60);
    let seconds = timer % 60;
    el.textContent = `⏱ ${minutes}:${seconds.toString().padStart(2, '0')}`;
  }
}

function startTimer() {
  if (interval !== null) return;
  interval = setInterval(() => {
    timer++;
    updateTimerDisplay();
  }, 1000);
}

/* ================================
RESET
================================ */
function resetGame() {
  path = [];
  currentNumber = 1;
  hintActive = false;
  gameOver = false;
  createGrid();
  redrawCanvas();
}

/* ================================
WIN
================================ */
function checkWin() {

  // must fill all cells
  if (path.length !== size * size) return;

  // must reach last number
  const maxNumber = getMaxNumber(gridData);
  if (currentNumber !== maxNumber + 1) return;

  // prevent multiple triggers
  if (gameOver) return;

  // ✅ REAL WIN
  gameOver = true;
  clearInterval(interval);

  gamesPlayed++;
  zipNumber++;

  // 🔥 animation only here
  playWinAnimation();

  setTimeout(() => {
    alert("🎉 Completed! Time: " +
      (timer < 60
        ? timer + "s"
        : Math.floor(timer / 60) + ":" + (timer % 60).toString().padStart(2, '0'))
    );

    loadNextPuzzle();
  }, 500);
}

function playWinAnimation() {

  // FLASH
  const flash = document.createElement("div");
  flash.className = "win-flash";
  document.body.appendChild(flash);

  setTimeout(() => flash.remove(), 800);

  // PARTICLES
  let canvas = document.createElement("canvas");
  canvas.id = "winCanvas";
  document.body.appendChild(canvas);

  let ctx = canvas.getContext("2d");

  canvas.width = window.innerWidth;
  canvas.height = window.innerHeight;

  let particles = [];

  for (let i = 0; i < 80; i++) {
    particles.push({
      x: canvas.width / 2,
      y: canvas.height / 2,
      vx: (Math.random() - 0.5) * 10,
      vy: (Math.random() - 0.5) * 10,
      size: Math.random() * 4 + 2,
      life: 100
    });
  }

  function animate() {
    ctx.clearRect(0, 0, canvas.width, canvas.height);

    particles.forEach(p => {
      p.x += p.vx;
      p.y += p.vy;
      p.life--;

      ctx.beginPath();
      ctx.arc(p.x, p.y, p.size, 0, Math.PI * 2);
      ctx.fillStyle = "rgba(0,255,255,0.8)";
      ctx.fill();
    });

    particles = particles.filter(p => p.life > 0);

    if (particles.length > 0) {
      requestAnimationFrame(animate);
    } else {
      canvas.remove();
    }
  }

  animate();
}

/* ================================
INIT
================================ */
loadNextPuzzle();