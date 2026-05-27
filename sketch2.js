/*
CREATE LINE
-> MOVE STEP
-> STORE POINT
-> RANDOM TURN
-> REPEAT
-> DRAW PATH
*/

let distLength = 50;
let stations = [];
let lines = [];
let stops = [];
let joins = [];
let gridPoints = [];
let gridBounds = null;
let allSegments = [];
let central = {}; 
let centralHubs = [];
let polySynth; 

const EPSILON = 0.001;
const SHOW_HUB_DEBUG = false;
const TURN_WINDOW = 4;
const MAX_TURNS_IN_WINDOW = 1;
const MIN_TURNS_PER_LINE = 4;
const MAX_TURNS_PER_LINE = 7;
const HUB_REACH_RADIUS = 1.3;
const HUB_SPREAD_STEPS = 2;
const HUB_PULL_WEIGHT = 0.85;
const CENTER_CLUSTER_RADIUS = 5;
const ALLOW_CENTER_CROSSINGS = true;
const CENTER_COLLISION_PENALTY = 0.1;
const OUTER_COLLISION_PENALTY = 1.0;
const MIN_OUTER_STRAIGHT = 2;
const MAX_OUTER_STRAIGHT = 5;
const MIN_CENTER_STRAIGHT = 2;
const MAX_CENTER_STRAIGHT = 4;
const MIN_STRAIGHT_AFTER_TURN = 3;
const MAX_STRAIGHT_AFTER_TURN = 6;
const MIN_STRAIGHT_BEFORE_STEER = 4;
const MIN_POST_HUB_STEPS = 3;
const MAX_POST_HUB_STEPS = 5;
const MIN_CENTRAL_BOX_STEPS = 3;
const PARALLEL_AXIS_TOL_STEPS = 1.2; //how close is too close
const PARALLEL_AXIS_OVERLAP_STEPS = 0.8; 
const PARALLEL_AXIS_ALLOW_OVERLAP_STEPS = 0.45; //short overlap allowed
const PARALLEL_AXIS_MAX_NEARBY = 0; //how many near-parallel lines are allowed
const PARALLEL_DIAG_TOL_STEPS = 0.65;
const PARALLEL_DIAG_OVERLAP_STEPS = 0.9;
const PARALLEL_CENTER_RELAX = 1.08;
const PARALLEL_CENTER_MAX_NEARBY = 0;
const TERMINAL_MIN_BOX_STEPS = 3;
const NEAR_REVISIT_STEPS = 7;
const NEAR_REVISIT_RADIUS = 0.85;
const TERMINAL_AXIS_TOL = 0.5;
const FAMILY_COUNTS = {
    westEast: 2,
    northSouth: 2,
    swNe: 1,
    nwSe: 1,
    shortBranch: 1,
    centerBox: 1
};
const LINE_COLOR_PALETTE = [
    'F89925',
    'DCD0E4',
    '5E340E',
    '7FCDF1',
    '5BD0B6',
    'F8BA1B',
    'C5EDED',
    'FEBBE7',
    'FF75CE',
    '696331',
    '6BA5BD',
    'A9A834',
    'FFE47C',
    'B27A95',
    'F9AF50',
    '63C4CD',
    '96D466',
    'F7D76C',
    'F87A9E',
];
let lineColorOrder = [];
let lineColorIndex = 0;
let people = [];
let controlStations = [];
let nextPersonId = 1;
let nextLineId = 0;
let routesGenerated = false;
let animationTimer = null;
let smileyPulseSvg = null;
let stopSmileySvg = null;
let pulseStopCooldownByKey = new Map();
let lastPulsePositionByPerson = new Map();
let pulseStateByPerson = new Map();
let echoPulses = [];
let intersectionBursts = [];
let lineGlowUntil = new Map();
let pendingIntersectionMeetings = new Map();
let intersectionNamesByKey = new Map();
let stationAnchorByName = new Map();
const STOP_NOTE_POOL = ['D4', 'F#4', 'A4', 'C#5', 'D5', 'E5', 'F#5', 'A5', 'C#6'];
const STOP_HIT_COOLDOWN_MS = 2400;
const STOP_NOTE_VOLUME = 0.4;
const STOP_NOTE_DURATION = 0.2;
let audioUnlocked = false;
const BASE_TRAIN_SPEED = 1.0;
const BASE_PULSE_STEP_PER_SEC = 0.2;
const INTERSECTION_WAIT_MIN_MS = 1000;
const INTERSECTION_WAIT_MAX_MS = 2000;
const INTERSECTION_RELEASE_MS = 120;
const PASSIVE_CROSSING_COOLDOWN_MS = 700;
const FATE_ROUTE_MAX_TRIES = 40;
const ONBOARDING_STORAGE_KEY = 'central_onboarding_v1';
let panelStationNames = ['Gym', 'School', 'Cafe'];
const PANEL_COLOR_PALETTE = [
    '#D96B67',
    '#E0BD67',
    '#DD7AD2',
    '#9D8199',
    '#4F3D21',
    '#6F8ED8',
    '#4E8B5F',
    '#7891D4',
    '#A27EC4'
];
const startArea = {
    marginX: 180,
    marginY: 120
};

function directionToDelta(direction) {
    if (direction === 1) return [0, -1];
    if (direction === 2) return [1, -1];
    if (direction === 3) return [1, 0];
    if (direction === 4) return [1, 1];
    if (direction === 5) return [0, 1];
    if (direction === 6) return [-1, 1];
    if (direction === 7) return [-1, 0];
    if (direction === 8) return [-1, -1];
    return [0, 0];
}

function classifySegment(p1, p2) {
    const dx = p2[0] - p1[0];
    const dy = p2[1] - p1[1];

    if (abs(dx) < EPSILON) return 'vertical';
    if (abs(dy) < EPSILON) return 'horizontal';
    if (dx * dy > 0) return 'diagDown';
    return 'diagUp';
}

function isAxisKind(kind) {
    return kind === 'horizontal' || kind === 'vertical';
}

function isDiagonalKind(kind) {
    return kind === 'diagUp' || kind === 'diagDown';
}

function pointsEqual(a, b) {
    return abs(a[0] - b[0]) < EPSILON && abs(a[1] - b[1]) < EPSILON;
}

function pointOnGridVertex(p) {
    const gx = (p[0] - gridBounds.minX) / distLength;
    const gy = (p[1] - gridBounds.minY) / distLength;
    return abs(gx - round(gx)) < EPSILON && abs(gy - round(gy)) < EPSILON;
}

function makeSegment(p1, p2, lineId) {
    return {
        p1,
        p2,
        lineId,
        kind: classifySegment(p1, p2)
    };
}

function segmentIntersectionInclusive(p1, p2, p3, p4) {
    const x1 = p1[0], y1 = p1[1];
    const x2 = p2[0], y2 = p2[1];
    const x3 = p3[0], y3 = p3[1];
    const x4 = p4[0], y4 = p4[1];

    const denom = (x1 - x2) * (y3 - y4) - (y1 - y2) * (x3 - x4);
    if (abs(denom) < EPSILON) return null;

    const t = ((x1 - x3) * (y3 - y4) - (y1 - y3) * (x3 - x4)) / denom;
    const u = ((x1 - x3) * (y1 - y2) - (y1 - y3) * (x1 - x2)) / denom;
    if (t < -EPSILON || t > 1 + EPSILON || u < -EPSILON || u > 1 + EPSILON) return null;

    return [
        x1 + t * (x2 - x1),
        y1 + t * (y2 - y1)
    ];
}

function collinearAxisOverlap(a1, a2, b1, b2) {
    const aKind = classifySegment(a1, a2);
    const bKind = classifySegment(b1, b2);
    if (!isAxisKind(aKind) || !isAxisKind(bKind) || aKind !== bKind) return null;

    if (aKind === 'horizontal') {
        if (abs(a1[1] - b1[1]) >= EPSILON) return null;
        const left = max(min(a1[0], a2[0]), min(b1[0], b2[0]));
        const right = min(max(a1[0], a2[0]), max(b1[0], b2[0]));
        if (right - left < EPSILON) return null;
        return [
            [left, a1[1]],
            [right, a1[1]]
        ];
    }

    if (abs(a1[0] - b1[0]) >= EPSILON) return null;
    const top = max(min(a1[1], a2[1]), min(b1[1], b2[1]));
    const bottom = min(max(a1[1], a2[1]), max(b1[1], b2[1]));
    if (bottom - top < EPSILON) return null;
    return [
        [a1[0], top],
        [a1[0], bottom]
    ];
}

function segmentAngleDegrees(segA, segB) {
    const v1x = segA.p2[0] - segA.p1[0];
    const v1y = segA.p2[1] - segA.p1[1];
    const v2x = segB.p2[0] - segB.p1[0];
    const v2y = segB.p2[1] - segB.p1[1];
    const mag1 = sqrt(v1x * v1x + v1y * v1y);
    const mag2 = sqrt(v2x * v2x + v2y * v2y);
    const dot = abs(v1x * v2x + v1y * v2y);

    const ratio = constrain(dot / (mag1 * mag2), -1, 1);
    return degrees(acos(ratio));
}

function isSharedEndpointIntersection(segA, segB, point) {
    const onA = pointsEqual(point, segA.p1) || pointsEqual(point, segA.p2);
    const onB = pointsEqual(point, segB.p1) || pointsEqual(point, segB.p2);
    return onA && onB;
}

function isNearCentralBox(x, y, steps) {
    const margin = distLength * steps;
    return (
        x >= central.minX - margin &&
        x <= central.maxX + margin &&
        y >= central.minY - margin &&
        y <= central.maxY + margin
    );
}

function getCollisionPenalty(x, y) {
    if (isNearCentralBox(x, y, CENTER_CLUSTER_RADIUS)) {
        return CENTER_COLLISION_PENALTY;
    }
    return OUTER_COLLISION_PENALTY;
}

function axisOverlapLength(a1, a2, b1, b2) {
    const kind = classifySegment(a1, a2);
    if (kind === 'vertical') {
        const top = max(min(a1[1], a2[1]), min(b1[1], b2[1]));
        const bottom = min(max(a1[1], a2[1]), max(b1[1], b2[1]));
        return max(0, bottom - top);
    }
    if (kind === 'horizontal') {
        const left = max(min(a1[0], a2[0]), min(b1[0], b2[0]));
        const right = min(max(a1[0], a2[0]), max(b1[0], b2[0]));
        return max(0, right - left);
    }
    return 0;
}

function segmentLength(p1, p2) {
    return dist(p1[0], p1[1], p2[0], p2[1]);
}

function isNearParallelAxis(candidate, existing, relaxFactor = 1) {
    if (candidate.kind !== existing.kind) return false;
    if (!isAxisKind(candidate.kind)) return false;

    const tol = distLength * PARALLEL_AXIS_TOL_STEPS * relaxFactor;
    const overlapThreshold = distLength * PARALLEL_AXIS_OVERLAP_STEPS * relaxFactor;
    const allowOverlap = distLength * PARALLEL_AXIS_ALLOW_OVERLAP_STEPS;

    if (candidate.kind === 'vertical') {
        if (abs(candidate.p1[0] - existing.p1[0]) > tol) return false;
    } else {
        if (abs(candidate.p1[1] - existing.p1[1]) > tol) return false;
    }

    const overlap = axisOverlapLength(candidate.p1, candidate.p2, existing.p1, existing.p2);
    if (overlap <= allowOverlap) return false;
    return overlap >= overlapThreshold;
}

function isNearParallelDiagonal(candidate, existing, relaxFactor = 1) {
    if (candidate.kind !== existing.kind) return false;
    if (!isDiagonalKind(candidate.kind)) return false;

    const tol = distLength * PARALLEL_DIAG_TOL_STEPS * relaxFactor;
    const overlapThreshold = distLength * PARALLEL_DIAG_OVERLAP_STEPS * relaxFactor;

    const midA = [(candidate.p1[0] + candidate.p2[0]) / 2, (candidate.p1[1] + candidate.p2[1]) / 2];
    const midB = [(existing.p1[0] + existing.p2[0]) / 2, (existing.p1[1] + existing.p2[1]) / 2];
    if (dist(midA[0], midA[1], midB[0], midB[1]) > tol) return false;

    return min(segmentLength(candidate.p1, candidate.p2), segmentLength(existing.p1, existing.p2)) >= overlapThreshold;
}

function getParallelProximityPenalty(candidate) {
    let penalty = 0;
    const candidateNearCenter = isNearCentralBox(candidate.p1[0], candidate.p1[1], CENTER_CLUSTER_RADIUS) ||
        isNearCentralBox(candidate.p2[0], candidate.p2[1], CENTER_CLUSTER_RADIUS);

    for (const seg of allSegments) {
        if (seg.lineId === candidate.lineId) continue;

        const segNearCenter = isNearCentralBox(seg.p1[0], seg.p1[1], CENTER_CLUSTER_RADIUS) ||
            isNearCentralBox(seg.p2[0], seg.p2[1], CENTER_CLUSTER_RADIUS);
        const centerContext = candidateNearCenter && segNearCenter;
        const relaxFactor = centerContext ? PARALLEL_CENTER_RELAX : 1;

        if (isNearParallelAxis(candidate, seg, relaxFactor)) {
            penalty += centerContext ? 2.2 : 1.2;
        }

        if (isNearParallelDiagonal(candidate, seg, relaxFactor)) {
            penalty += centerContext ? 2.8 : 1.6;
        }
    }

    return penalty;
}

function isSegmentAllowed(candidate) {
    const candidateNearCenter = isNearCentralBox(candidate.p1[0], candidate.p1[1], CENTER_CLUSTER_RADIUS) ||
        isNearCentralBox(candidate.p2[0], candidate.p2[1], CENTER_CLUSTER_RADIUS);
    let nearbyParallelCount = 0;
    const currentLine = lines.find(line => line.id === candidate.lineId) || null;
    const intersectionChance = currentLine ? currentLine.intersectionChance || 0.4 : 0.4;
    const permissiveIntersection = random() < intersectionChance;

    for (const seg of allSegments) {
        const segNearCenter = isNearCentralBox(seg.p1[0], seg.p1[1], CENTER_CLUSTER_RADIUS) ||
            isNearCentralBox(seg.p2[0], seg.p2[1], CENTER_CLUSTER_RADIUS);
        const overlap = collinearAxisOverlap(candidate.p1, candidate.p2, seg.p1, seg.p2);
        if (overlap) {
            // Corridor merge is allowed only on horizontal/vertical segments.
            continue;
        }

        const centerParallelContext = candidateNearCenter && segNearCenter;
        const relaxFactor = centerParallelContext ? PARALLEL_CENTER_RELAX : 1;
        const maxNearby = centerParallelContext ? PARALLEL_CENTER_MAX_NEARBY : PARALLEL_AXIS_MAX_NEARBY;

        if (isNearParallelAxis(candidate, seg, relaxFactor) && random() > intersectionChance * 0.75) {
            nearbyParallelCount++;
            if (nearbyParallelCount > maxNearby) return false;
        }

        if (isNearParallelDiagonal(candidate, seg, relaxFactor) && random() > intersectionChance * 0.6) return false;

        const hit = segmentIntersectionInclusive(candidate.p1, candidate.p2, seg.p1, seg.p2);
        if (!hit) continue;
        if (isSharedEndpointIntersection(candidate, seg, hit)) continue;

        const inCenterCrossZone = ALLOW_CENTER_CROSSINGS && isNearCentralBox(hit[0], hit[1], CENTER_CLUSTER_RADIUS);
        if (inCenterCrossZone) {
            if (permissiveIntersection || intersectionChance >= 0.55) continue;
            return false;
        }

        if (!inCenterCrossZone) {
            if (isDiagonalKind(candidate.kind) && isDiagonalKind(seg.kind)) return false;
            if (!pointOnGridVertex(hit)) return false;

            const angle = segmentAngleDegrees(candidate, seg);
            const angleIs45 = abs(angle - 45) < 0.2;
            const angleIs90 = abs(angle - 90) < 0.2;
            if (!angleIs45 && !angleIs90) return false;
            if (!permissiveIntersection) return false;
        }
    }

    return true;
}

//CREATE A LINE
// position (x, y) direction list of points
class Line {
    constructor (x, y, direction, id, targetHub, endpointTarget = null, options = {}) {
        this.startX = x;
        this.startY = y;
        this.startDirection = direction;

        this.x = x;
        this.y = y;
        this.direction = direction;
        this.id = id;
        this.targetHub = targetHub;
        this.endpointTarget = endpointTarget;
        this.secondaryHub = options.secondaryHub || null;
        this.secondaryHubReached = false;

        this.enteredHub = false;
        this.exitedHub = false;
        this.touchedCentralBox = false;
        this.postHubSteps = 0;
        this.requiredPostHubSteps = floor(random(MIN_POST_HUB_STEPS, MAX_POST_HUB_STEPS + 1));

        this.maxTurns = floor(random(MIN_TURNS_PER_LINE, MAX_TURNS_PER_LINE + 1));
        this.turnCount = 0;
        this.recentTurnFlags = [];
        this.recentTurnSteps = [];
        this.turnCooldown = 0;
        this.straightStreak = 0;
        this.stepsSinceTurn = 0;
        this.requiredStraightAfterTurn = floor(random(MIN_STRAIGHT_AFTER_TURN, MAX_STRAIGHT_AFTER_TURN + 1));
        this.stepDirHistory = [];
        this.minStraightBeforeTurn = floor(random(MIN_OUTER_STRAIGHT, MAX_OUTER_STRAIGHT + 1));
        this.visitedKeys = new Set([pointKeyXY(x, y)]);

        const [vx, vy] = directionToDelta(direction);
        this.vx = vx;
        this.vy = vy;
        this.points = [[x, y]];
        if (!lineColorOrder.length || lineColorIndex >= lineColorOrder.length) {
            lineColorOrder = shuffleArray(LINE_COLOR_PALETTE.slice());
            lineColorIndex = 0;
        }
        const hex = lineColorOrder[lineColorIndex++];
        this.lineColor = hexToRgbArray(hex);
        this.strokeW = 4;
        this.intersectionChance = 0.4;
        this.speed = 1;
        this.personId = null;
    }

    //MOVE STEP
    /*
     8   1   2
      \  |  /
    7 -      - 3
      /  |  \
     6   5   4
    */
    move () {
        const wasInsideCentralBox = isInCentralBox(this.x, this.y);
        const nextX = this.x + this.vx * distLength;
        const nextY = this.y + this.vy * distLength;

        const insideGrid =
            nextX >= gridBounds.minX &&
            nextX <= gridBounds.maxX &&
            nextY >= gridBounds.minY &&
            nextY <= gridBounds.maxY;

        if (!insideGrid) return false;

        const nextPoint = [nextX, nextY];
        const prevPoint = this.points.length > 1 ? this.points[this.points.length - 2] : null;

        if (prevPoint && pointsEqual(nextPoint, prevPoint)) return false; // no immediate backtracking
        if (this.visitedKeys.has(pointKeyXY(nextX, nextY))) return false; // no returning to old points
        if (isNearRecentPoint(this.points, nextPoint, NEAR_REVISIT_STEPS, distLength * NEAR_REVISIT_RADIUS)) return false;
        if (createsSmallLoop(this.points, nextPoint)) return false;
        if (wouldCreateAlternatingStepPattern(this.stepDirHistory, this.direction)) return false;

        const candidate = makeSegment([this.x, this.y], [nextX, nextY], this.id);
        if (!isSegmentAllowed(candidate)) return false;

        this.x = nextX;
        this.y = nextY;
        this.points.push([this.x, this.y]);
        this.visitedKeys.add(pointKeyXY(this.x, this.y));
        allSegments.push(candidate);

        this.straightStreak++;
        this.stepsSinceTurn++;
        this.stepDirHistory.push(this.direction);
        if (this.stepDirHistory.length > 8) this.stepDirHistory.shift();
        if (this.turnCooldown > 0) this.turnCooldown--;

        if (!this.enteredHub && isInHubArea(this.x, this.y, this.targetHub)) {
            this.enteredHub = true;
        } else if (this.enteredHub && !isInCentralBox(this.x, this.y)) {
            this.exitedHub = true;
            this.postHubSteps++;
        }
        const isInsideCentralBox = isInCentralBox(this.x, this.y);
        if (isInsideCentralBox) {
            this.touchedCentralBox = true;
            this.centralBoxTravelSteps++;
        } else if (this.touchedCentralBox && wasInsideCentralBox) {
            this.exitedCentralBoxAfterTouch = true;
        }
        if (this.secondaryHub && !this.secondaryHubReached && isInHubArea(this.x, this.y, this.secondaryHub)) {
            this.secondaryHubReached = true;
        }

        return true;
    }

    canTurnNow () {
        return this.stepsSinceTurn >= this.requiredStraightAfterTurn;
    }

    registerTurn (turnStep) {
        const turned = turnStep !== 0;
        if (turned) {
            this.turnCount++;
            this.straightStreak = 0;
            this.stepsSinceTurn = 0;
            this.requiredStraightAfterTurn = floor(random(MIN_STRAIGHT_AFTER_TURN, MAX_STRAIGHT_AFTER_TURN + 1));
            this.turnCooldown = isInCentralBox(this.x, this.y) ? 1 : 2;
            this.minStraightBeforeTurn = isInCentralBox(this.x, this.y)
                ? floor(random(MIN_CENTER_STRAIGHT, MAX_CENTER_STRAIGHT + 1))
                : floor(random(MIN_OUTER_STRAIGHT, MAX_OUTER_STRAIGHT + 1));
        }

        this.recentTurnFlags.push(turned);
        this.recentTurnSteps.push(turnStep);
        if (this.recentTurnFlags.length > TURN_WINDOW) this.recentTurnFlags.shift();
        if (this.recentTurnSteps.length > TURN_WINDOW) this.recentTurnSteps.shift();
    }

    applySteerToward (targetDir, maxStep) {
        const nextDir = steerDirectionToward(this.direction, targetDir, maxStep);
        const diff = circularDiff(this.direction, nextDir);
        if (diff === 0) return false;

        const turnStep = diff > 0 ? 1 : -1;

        if (!canAcceptTurn(this, nextDir, turnStep)) {
            return false;
        }

        this.direction = nextDir;
        const [nvx, nvy] = directionToDelta(this.direction);
        this.vx = nvx;
        this.vy = nvy;
        this.registerTurn(turnStep);
        return true;
    }

    //Draw the line by connecting points
    drawLine () {
        push();
        blendMode(MULTIPLY);
        stroke(this.lineColor[0], this.lineColor[1], this.lineColor[2]);
        strokeWeight(this.strokeW || 4);
        noFill();

        drawRoundedPolyline(this.points, 15);
        pop();
    }

    //RANDOM TURN
    changeDirection (forceTurn = false) {
        const phase = getLinePhase(this);
        let turnChance = random(0.30, 0.35); // before center
        if (phase === 'throughCenter') turnChance = random(0.45, 0.60);
        if (phase === 'toEnd') turnChance = random(0.35, 0.45);

        if (this.turnCount >= this.maxTurns) turnChance *= 0.2;

        const recentTurns = this.recentTurnFlags.slice(-TURN_WINDOW + 1).filter(Boolean).length;
        if (recentTurns >= MAX_TURNS_IN_WINDOW) turnChance *= 0.1;

        if (this.straightStreak < this.minStraightBeforeTurn) turnChance *= 0.35;
        if (this.turnCooldown > 0) turnChance *= 0.15;
        if (this.stepsSinceTurn < this.requiredStraightAfterTurn) turnChance = 0;
        if (forceTurn) turnChance = max(turnChance, 0.7);

        const desiredDir = this.getDesiredDirection(phase);

        const options = [
            { turnStep: 0, dir: this.direction },
            { turnStep: -1, dir: wrapDirection(this.direction - 1) },
            { turnStep: 1, dir: wrapDirection(this.direction + 1) }
        ].filter(o => o.dir !== oppositeDirection(this.direction));

        const minStraightGate = this.stepsSinceTurn >= this.requiredStraightAfterTurn;
        const gatedOptions = minStraightGate ? options : options.filter(o => o.turnStep === 0);

        for (const o of gatedOptions) {
            if (!canAcceptTurn(this, o.dir, o.turnStep)) {
                o.score = -9999;
                continue;
            }
            const diff = absCircularDiff(o.dir, desiredDir);
            let score = 20 - diff * 6;
            score += (4 - diff) * HUB_PULL_WEIGHT * 2;
            if (o.turnStep === 0) score += 5;
            if (phase === 'toEnd' && o.turnStep !== 0) score += 2;
            const [dx, dy] = directionToDelta(o.dir);
            const nextX = this.x + dx * distLength;
            const nextY = this.y + dy * distLength;
            score -= getCollisionPenalty(nextX, nextY) * 8;
            const candidate = makeSegment([this.x, this.y], [nextX, nextY], this.id);
            score -= getParallelProximityPenalty(candidate) * 6;
            o.score = score;
        }

        const validOptions = gatedOptions.filter(o => o.score > -9999);
        if (!validOptions.length) return;

        validOptions.sort((a, b) => b.score - a.score);

        let chosen = validOptions[0];
        if (random() < turnChance) {
            const turning = validOptions.filter(o => o.turnStep !== 0);
            if (turning.length) chosen = weightedPickByScore(turning);
        } else {
            chosen = validOptions.find(o => o.turnStep === 0) || validOptions[0];
        }

        this.registerTurn(chosen.turnStep);

        this.direction = chosen.dir;
        const [vx, vy] = directionToDelta(this.direction);
        this.vx = vx;
        this.vy = vy;
    }

    //RUN THE LINE
    run () {
        const minTravelSteps = 7; // to prevent very short lines that don't interact well with the system, especially in the center
        const directGridSteps = this.endpointTarget
            ? ceil(dist(this.startX, this.startY, this.endpointTarget.x, this.endpointTarget.y) / distLength)
            : 18;
        const maxTravelSteps = constrain(directGridSteps + 7, 22, 44); 
        const maxAttempts = 1000; //max number of move attempts (incluing failed one)
        const maxRouteRetries = 60; // how many times to restart the line if it fails to meet criteria
        let success = false;

        for (let routeTry = 0; routeTry < maxRouteRetries; routeTry++) {
            this.resetForRetry();
            let movedCount = 0;
            let attempts = 0;
            let reachedEnd = false;

            while (movedCount < maxTravelSteps && attempts < maxAttempts) {
                const phase = getLinePhase(this);
                if (phase === 'toCenter' && random() < 0.82) {
                    const targetDir = directionTowardCentral(this.x, this.y, this.targetHub);
                    this.applySteerToward(targetDir, 1);
                } else if (phase === 'throughCenter' && this.stepsSinceTurn >= MIN_STRAIGHT_BEFORE_STEER && random() < 0.70) {
                    const centerDir = this.getDesiredDirection('throughCenter');
                    this.applySteerToward(centerDir, 1);
                } else if (phase === 'toEnd' && this.stepsSinceTurn >= MIN_STRAIGHT_BEFORE_STEER && random() < 0.68) {
                    const outDir = directionTowardCentral(this.x, this.y, this.endpointTarget);
                    this.applySteerToward(outDir, 1);
                }

                const moved = this.move();
                attempts++;

                if (moved) {
                    movedCount++;

                reachedEnd = this.endpointTarget &&
                    dist(this.x, this.y, this.endpointTarget.x, this.endpointTarget.y) < distLength * 2.2;
                if (reachedEnd) break;
                } else {
                    if (phase === 'toCenter') {
                        const hubDir = directionTowardCentral(this.x, this.y, this.targetHub);
                        this.applySteerToward(hubDir, 2);
                        this.changeDirection(true);
                        continue;
                    }

                    if (phase === 'throughCenter') {
                        const centerDir = this.getDesiredDirection('throughCenter');
                        this.applySteerToward(centerDir, 2);
                        this.changeDirection(true);
                        continue;
                    }

                    if (this.postHubSteps < this.requiredPostHubSteps) {
                        const outDir = this.getDesiredDirection('toEnd');
                        this.applySteerToward(outDir, 2);
                        this.changeDirection(true);
                        continue;
                    }

                    if (!this.endpointTarget && movedCount >= minTravelSteps) break;
                }

                this.changeDirection();
            }

            this.endOutsideCentralBox = !isInCentralBox(this.x, this.y);
            success =
                this.enteredHub &&
                this.touchedCentralBox &&
                this.exitedCentralBoxAfterTouch &&
                this.centralBoxTravelSteps >= MIN_CENTRAL_BOX_STEPS &&
                !isInCentralBox(this.startX, this.startY) &&
                this.postHubSteps >= this.requiredPostHubSteps &&
                movedCount >= minTravelSteps &&
                (!this.endpointTarget || reachedEnd) &&
                this.endOutsideCentralBox;
            if (success) break;
        }

        if (!success) {
            this.resetForRetry();
            return;
        } 

        this.ensureTerminalOutsideCentral();
        this.points = mergeNearbyTurns(this.points);
        this.drawLine();
    }

    ensureTerminalOutsideCentral () {
        const last = this.points[this.points.length - 1];
        if (!isInCentralBox(last[0], last[1])) return;

        for (let i = 0; i < 24; i++) {
            const outDir = directionAwayFromCentral(this.x, this.y);
            this.applySteerToward(outDir, 2);

            let moved = this.move();
            if (!moved && this.stepsSinceTurn >= this.requiredStraightAfterTurn) {
                this.changeDirection(true);
                moved = this.move();
            }

            if (!moved) break;
            const p = this.points[this.points.length - 1];
            if (!isInCentralBox(p[0], p[1])) break;
        }
    }

    getDesiredDirection (phase) {
        if (phase === 'toCenter') {
            return directionTowardCentral(this.x, this.y, this.targetHub);
        }

        if (phase === 'throughCenter') {
            if (this.secondaryHub && !this.secondaryHubReached && isInCentralBox(this.x, this.y)) {
                return directionTowardCentral(this.x, this.y, this.secondaryHub);
            }
            return directionTowardCentral(this.x, this.y, this.targetHub);
        }

        if (this.secondaryHub && !this.secondaryHubReached && isInCentralBox(this.x, this.y)) {
            return directionTowardCentral(this.x, this.y, this.secondaryHub);
        }

        if (this.endpointTarget) {
            return directionTowardCentral(this.x, this.y, this.endpointTarget);
        }

        return directionAwayFromCentral(this.x, this.y);
    }

    resetForRetry () {
        allSegments = allSegments.filter(seg => seg.lineId !== this.id);

        this.x = this.startX;
        this.y = this.startY;
        this.enteredHub = false;
        this.exitedHub = false;
        this.touchedCentralBox = false;
        this.exitedCentralBoxAfterTouch = false;
        this.centralBoxTravelSteps = 0;
        this.endOutsideCentralBox = false;
        this.secondaryHubReached = false;
        this.postHubSteps = 0;
        this.turnCount = 0;
        this.recentTurnFlags = [];
        this.recentTurnSteps = [];
        this.turnCooldown = 0;
        this.straightStreak = 0;
        this.stepsSinceTurn = 0;
        this.requiredStraightAfterTurn = floor(random(MIN_STRAIGHT_AFTER_TURN, MAX_STRAIGHT_AFTER_TURN + 1));
        this.stepDirHistory = [];
        this.minStraightBeforeTurn = floor(random(MIN_OUTER_STRAIGHT, MAX_OUTER_STRAIGHT + 1));
        this.points = [[this.startX, this.startY]];
        this.visitedKeys = new Set([pointKeyXY(this.startX, this.startY)]);

        const refreshedDir = directionTowardCentral(this.startX, this.startY, this.targetHub);
        this.direction = steerDirectionToward(this.startDirection, refreshedDir, 2);
        const [vx, vy] = directionToDelta(this.direction);
        this.vx = vx;
        this.vy = vy;
    }
}

function buildGrid(minX, maxX, minY, maxY, spacing) {
    const points = [];
    for (let x = minX; x <= maxX; x += spacing) {
        for (let y = minY; y <= maxY; y += spacing) {
            points.push({ x, y });
        }
    }
    return points;
}

function preload() {
    smileyPulseSvg = loadImage('rectangle smiley.svg');
    stopSmileySvg = loadImage('relax smiley.svg');
}

function setup () {
    const onboarding = loadOnboardingData();
    panelStationNames = onboarding.places;

    const canvas = createCanvas(windowWidth, windowHeight);
    canvas.parent('canvas-wrap');
    background('#FBF4E1');
    polySynth = new p5.PolySynth();
    if (typeof polySynth.setADSR === 'function') {
        polySynth.setADSR(0.1, 0.4, 0.1, 2);
    }
    if (typeof polySynth.setOscillator === 'function') {
        polySynth.setOscillator('triangle');
    }
    enableSoundOnFirstGesture();

    stations = [];
    lines = [];
    stops = [];
    joins = [];
    people = [];
    controlStations = panelStationNames.map(name => ({ name, people: [] }));
    nextPersonId = 1;
    allSegments = [];
    lineColorOrder = shuffleArray(LINE_COLOR_PALETTE.slice());
    lineColorIndex = 0;
    nextLineId = 0;
    routesGenerated = false;

    const minX = min(startArea.marginX, width / 2);
    const maxX = max(width - startArea.marginX, width / 2);
    const minY = min(startArea.marginY, height / 2);
    const maxY = max(height - startArea.marginY, height / 2);
    gridBounds = { minX, maxX, minY, maxY };
    gridPoints = buildGrid(minX, maxX, minY, maxY, distLength);

    if (gridPoints.length === 0) return;

    //Define central box
    const centerX = (minX + maxX) / 2;
    const centerY = (minY + maxY) / 2;
    // Central interaction zone: slightly larger to allow varied interchange points.
    const coreWidth = (maxX - minX) * 0.46;
    const coreHeight = (maxY - minY) * 0.46;

    central = {
        minX: centerX - coreWidth / 2, //left edge
        maxX: centerX + coreWidth / 2, //right edge
        minY: centerY - coreHeight / 2, //top edge
        maxY: centerY + coreHeight / 2 //bottom edge
    };

    centralHubs = getCentralHubPoints();
    initializePrimaryUserRoute(onboarding);
    routesGenerated = true;
    setupUI();
    renderLegend();
    refreshAnimationLoop();
}

function draw () {
    background('#FBF4E1');

    drawGridVertices();
    drawHubs(); 
    drawCentralBox();

    for (const person of people) {
        drawTrainLine(person);
    }

    // drawJoins();
    drawEchoPulses();
    drawStops();
    drawStartPoints();
    drawTrainPulses();
    drawIntersectionBursts();

    noLoop();
}

function loadOnboardingData() {
    const fallback = {
        stages: 'My Route',
        places: ['Gym', 'School', 'Cafe']
    };
    const raw = localStorage.getItem(ONBOARDING_STORAGE_KEY);
    if (!raw) return fallback;

    try {
        const parsed = JSON.parse(raw);
        const stages = parsed && parsed.stages ? `${parsed.stages}`.trim() : fallback.stages;
        const places = Array.isArray(parsed && parsed.places)
            ? parsed.places.slice(0, 3).map((name, index) => `${name || ''}`.trim() || fallback.places[index])
            : fallback.places;
        return {
            stages: stages || fallback.stages,
            places: places.length === 3 ? places : fallback.places
        };
    } catch (err) {
        return fallback;
    }
}

function initializePrimaryUserRoute(onboarding) {
    const firstStation = panelStationNames[0] || 'Station 1';
    const primary = buildPerson(onboarding.stages || 'My Route', firstStation);
    primary.stations = panelStationNames.slice();
    primary.isPrimary = true;
    people.push(primary);

    for (const station of controlStations) {
        if (!station.people.includes(primary.id)) station.people.push(primary.id);
    }

    generateLineForPerson(primary);
    addStops();
}

function setupUI() {
    setupTabs();
    renderStations();
    renderTrains();
}

function setupTabs() {
    const tabs = document.querySelectorAll('.tab');
    tabs.forEach(tab => {
        tab.addEventListener('click', () => {
            const target = tab.dataset.tab;

            document.querySelectorAll('.tab').forEach(item => item.classList.remove('active'));
            document.querySelectorAll('.tabContent').forEach(content => content.classList.remove('active'));

            tab.classList.add('active');
            const content = document.getElementById(`${target}Tab`);
            if (content) content.classList.add('active');
        });
    });
}

function renderLegend() {
    const box = document.getElementById('nameBox');
    if (!box) return;
    box.innerHTML = '';

    for (const person of people) {
        const row = document.createElement('div');
        row.className = 'nameRow';

        const name = document.createElement('div');
        name.className = 'nameLabel';
        name.textContent = person.name;

        const swatch = document.createElement('input');
        swatch.type = 'color';
        swatch.className = 'colorSwatch';
        swatch.value = normalizeHexColor(person.color);
        swatch.dataset.personId = `${person.id}`;
        swatch.addEventListener('input', handleLegendColorInput);

        row.appendChild(name);
        row.appendChild(swatch);
        box.appendChild(row);
    }
}

function handleLegendColorInput(event) {
    const input = event.target;
    const personId = Number(input.dataset.personId);
    if (!personId) return;

    const person = people.find(entry => entry.id === personId);
    if (!person) return;

    person.color = normalizeHexColor(input.value);
    const line = findLineByPersonId(person.id);
    if (line) {
        line.lineColor = hexToRgbArray(person.color);
    }

    renderTrains();
    redraw();
}

function renderStations() {
    const stationList = document.getElementById('stationList');
    if (!stationList) return;
    stationList.innerHTML = '';

    for (const station of controlStations) {
        const card = document.createElement('div');
        card.className = 'stationCard';

        const title = document.createElement('div');
        title.className = 'stationTitle';
        title.innerHTML = `<span class="stationDot"></span><span>${station.name}</span>`;

        const chipWrap = document.createElement('div');
        chipWrap.className = 'chipWrap';
        if (!station.people.length) {
            const hint = document.createElement('p');
            hint.className = 'emptyHint';
            hint.textContent = 'No people yet.';
            chipWrap.appendChild(hint);
        } else {
            for (const personId of station.people) {
                const person = people.find(entry => entry.id === personId);
                if (!person) continue;

                const chip = document.createElement('span');
                chip.className = 'nameChip';
                chip.textContent = person.name;
                chipWrap.appendChild(chip);
            }
        }

        const inputRow = document.createElement('div');
        inputRow.className = 'inputRow';

        const input = document.createElement('input');
        input.type = 'text';
        input.placeholder = 'Add person';

        const button = document.createElement('button');
        button.type = 'button';
        button.textContent = 'Add';
        button.addEventListener('click', () => {
            const value = input.value.trim();
            if (!value) return;
            addPerson(value, station.name);
            input.value = '';
        });
        input.addEventListener('keydown', (event) => {
            if (event.key !== 'Enter') return;
            button.click();
        });

        inputRow.appendChild(input);
        inputRow.appendChild(button);
        card.appendChild(title);
        card.appendChild(chipWrap);
        card.appendChild(inputRow);
        stationList.appendChild(card);
    }
}

function renderTrains() {
    const trainList = document.getElementById('trainList');
    if (!trainList) return;
    trainList.innerHTML = '';
    let renderedCount = 0;

    for (const person of people) {
        if (person.isPrimary) continue;
        const card = document.createElement('div');
        card.className = 'trainCard';
        card.innerHTML = `
            <div class="trainHeader">
                <div class="trainColor" style="background:${person.color};"></div>
                <div class="trainName">${person.name}</div>
                <div class="stationCount">${person.stations.length} station${person.stations.length === 1 ? '' : 's'}</div>
            </div>
            <label class="sliderLabel">
                <span>CLOSENESS / EFFORT</span>
                <span>${person.closeness}</span>
            </label>
            <input type="range" min="1" max="5" step="1" value="${person.closeness}" data-person-id="${person.id}" data-control="closeness">
            <label class="sliderLabel">
                <span>FATE / POSSIBILITY</span>
                <span>${person.fate}</span>
            </label>
            <input type="range" min="1" max="5" step="1" value="${person.fate}" data-person-id="${person.id}" data-control="fate">
        `;
        trainList.appendChild(card);
        renderedCount++;
    }

    if (renderedCount === 0) {
        const hint = document.createElement('p');
        hint.className = 'emptyHint';
        hint.textContent = 'Add someone at a station to create a train card.';
        trainList.appendChild(hint);
    }

    trainList.querySelectorAll('input[type="range"]').forEach(slider => {
        slider.addEventListener('input', handleTrainSlider);
    });
}

function addPerson(name, stationName) {
    const normalizedName = `${name}`.trim();
    if (!normalizedName) return;

    const existing = people.find(person => person.name.toLowerCase() === normalizedName.toLowerCase());
    if (existing) {
        if (!existing.stations.includes(stationName)) {
            existing.stations.push(stationName);
        }

        const station = findStationByName(stationName);
        if (station && !station.people.includes(existing.id)) {
            station.people.push(existing.id);
        }

        regenerateLine(existing);
    } else {
        const person = buildPerson(normalizedName, stationName);
        people.push(person);

        const station = findStationByName(stationName);
        if (station) station.people.push(person.id);

        generateLineForPerson(person);
    }

    renderStations();
    renderTrains();
    renderLegend();
    refreshAnimationLoop();
    redraw();
}

function handleTrainSlider(event) {
    const slider = event.target;
    const personId = Number(slider.dataset.personId);
    const control = slider.dataset.control;
    const value = Number(slider.value);
    if (!personId || !control || !value) return;

    if (control === 'closeness') {
        updatePersonCloseness(personId, value);
    } else if (control === 'fate') {
        updatePersonFate(personId, value);
    }

    renderTrains();
    redraw();
}

function updatePersonCloseness(personId, value) {
    const person = people.find(entry => entry.id === personId);
    if (!person) return;

    person.closeness = value;
    person.strokeWeight = mapValue(value, 1, 5, 1.5, 8);
    const line = findLineByPersonId(person.id);
    if (line) line.strokeW = person.strokeWeight;
}

function updatePersonFate(personId, value) {
    const person = people.find(entry => entry.id === personId);
    if (!person) return;

    person.fate = value;
    const profile = getFateProfile(value);
    person.intersectionChance = profile.routeIntersectionChance;
    person.centralMeetingChance = profile.centralMeetingChance;
    person.sideMeetingChance = profile.sideMeetingChance;
    person.centralTargetIntersections = profile.centralTargetIntersections;
    person.centralStopsEnabled = profile.centralStopsEnabled;
    person.waitMultiplier = profile.waitMultiplier;
    person.speed = BASE_TRAIN_SPEED;

    regenerateLine(person);
    refreshAnimationLoop();
}

function regenerateLine(person) {
    if (!person) return;

    const line = findLineByPersonId(person.id);
    if (!line) {
        generateLineForPerson(person);
        return;
    }

    line.strokeW = person.strokeWeight;
    line.intersectionChance = person.intersectionChance;
    line.speed = BASE_TRAIN_SPEED;
    line.lineColor = hexToRgbArray(person.color);
    rerouteLineForFateProfile(person, line);
    syncPersonPathFromLine(person);
    addStops();
}

function generateLineForPerson(person) {
    const profile = getFateProfile(person.fate);
    let bestCandidate = null;
    let bestScore = Infinity;

    for (let attempt = 0; attempt < FATE_ROUTE_MAX_TRIES; attempt++) {
        const spec = pickRouteSpecForPerson(person);
        const start = spec.start;
        const dir = directionTowardCentral(start.x, start.y, spec.hub);
        const candidate = new Line(
            start.x,
            start.y,
            dir,
            nextLineId,
            spec.hub,
            spec.end,
            { secondaryHub: spec.secondaryHub || null }
        );

        candidate.personId = person.id;
        candidate.strokeW = person.strokeWeight;
        candidate.intersectionChance = person.intersectionChance;
        candidate.speed = BASE_TRAIN_SPEED;
        candidate.lineColor = hexToRgbArray(person.color);
        candidate.run();
        if (!candidate.points || candidate.points.length < 2) continue;

        const stats = getCentralIntersectionStatsForLine(candidate);
        const score = getFateFitScore(profile, stats);
        if (score < bestScore) {
            bestScore = score;
            bestCandidate = candidate;
        }
        if (score === 0) break;
    }

    const line = bestCandidate;
    if (!line) return;
    lines.push(line);
    nextLineId++;
    person.lineId = line.id;
    syncPersonPathFromLine(person);
    addStops();
}

function buildPerson(name, stationName, existingLine = null) {
    const id = nextPersonId++;
    const fateProfile = getFateProfile(3);
    const person = {
        id,
        name,
        stations: [stationName],
        color: existingLine ? rgbArrayToCssHex(existingLine.lineColor) : getRandomMutedColor(),
        closeness: 5,
        fate: 3,
        strokeWeight: mapValue(5, 1, 5, 1.5, 8),
        speed: BASE_TRAIN_SPEED,
        intersectionChance: fateProfile.routeIntersectionChance,
        centralMeetingChance: fateProfile.centralMeetingChance,
        sideMeetingChance: fateProfile.sideMeetingChance,
        centralTargetIntersections: fateProfile.centralTargetIntersections,
        centralStopsEnabled: fateProfile.centralStopsEnabled,
        waitMultiplier: fateProfile.waitMultiplier,
        path: [],
        lineId: existingLine ? existingLine.id : null
    };

    if (existingLine) {
        existingLine.personId = person.id;
        existingLine.strokeW = person.strokeWeight;
        existingLine.intersectionChance = person.intersectionChance;
        existingLine.speed = BASE_TRAIN_SPEED;
        existingLine.lineColor = hexToRgbArray(person.color);
    }

    return person;
}

function drawTrainLine(person) {
    if (!person || !person.path || person.path.length < 2) return;
    const line = findLineByPersonId(person.id);
    const now = millis();
    const glowUntil = line ? (lineGlowUntil.get(line.id) || 0) : 0;
    const glowLevel = glowUntil > now ? constrain((glowUntil - now) / 900, 0, 1) : 0;

    push();
    blendMode(MULTIPLY);
    if (glowLevel > 0) {
        stroke(person.color);
        strokeWeight(person.strokeWeight + mapValue(person.closeness, 1, 5, 3, 10) * glowLevel);
        stroke(255, 190, 120, 90 * glowLevel);
        noFill();
        drawRoundedPolyline(person.path, 15);
    }
    stroke(person.color);
    strokeWeight(person.strokeWeight);
    noFill();
    drawRoundedPolyline(person.path, 15);
    pop();
}

function drawTrainPulses() {
    if (!smileyPulseSvg) return;
    const now = millis();
    cleanupPendingIntersectionMeetings(now);

    for (const person of people) {
        if (!person.path || person.path.length < 2) continue;

        const pulse = getPulseState(person.id);
        const dtSec = max(0.001, (now - pulse.lastUpdatedAt) / 1000);
        pulse.lastUpdatedAt = now;
        if (now >= pulse.pausedUntil) {
            pulse.t += pulse.direction * BASE_PULSE_STEP_PER_SEC * dtSec * BASE_TRAIN_SPEED;
            if (pulse.t >= 1) {
                pulse.t = 1;
                pulse.direction = -1;
            } else if (pulse.t <= 0) {
                pulse.t = 0;
                pulse.direction = 1;
            }
        }

        const sample = samplePointOnPath(person.path, pulse.t);
        if (!sample) continue;
        const jitter = mapValue(person.fate, 1, 5, 0.35, 3.6);
        const ox = sin(now * 0.0012 + person.id) * jitter;
        const oy = cos(now * 0.0015 + person.id * 1.7) * jitter;

        const pulseSize = 26 + person.closeness * 4;
        handleIntersectionForPulse(person, pulse, sample.x + ox, sample.y + oy, pulseSize);
        const svgAspect = smileyPulseSvg.width > 0 && smileyPulseSvg.height > 0
            ? smileyPulseSvg.width / smileyPulseSvg.height
            : 1;
        const drawWidth = svgAspect >= 1 ? pulseSize : pulseSize * svgAspect;
        const drawHeight = svgAspect >= 1 ? pulseSize / svgAspect : pulseSize;
        push();
        translate(sample.x + ox, sample.y + oy);
        rotate(sample.angle || 0);
        imageMode(CENTER);
        tint(255, 210);
        image(smileyPulseSvg, 0, 0, drawWidth, drawHeight);
        pop();
    }
}

function getPulseState(personId) {
    let state = pulseStateByPerson.get(personId);
    if (!state) {
        state = {
            t: random(0.08, 0.25),
            direction: 1,
            pausedUntil: 0,
            lastUpdatedAt: millis(),
            waitingStopKey: null
        };
        pulseStateByPerson.set(personId, state);
    }
    return state;
}

function handleIntersectionForPulse(person, pulse, x, y, pulseSize) {
    if (!stops.length) return;
    const line = findLineByPersonId(person.id);
    if (!line) return;

    const now = millis();
    const hitRadius = max(18, pulseSize * 0.45);
    const previous = lastPulsePositionByPerson.get(person.id) || { x, y };

    for (const stop of stops) {
        if (!stop.lines.includes(line.id) || stop.lines.length < 2) continue;

        const directHit = dist(x, y, stop.point[0], stop.point[1]) <= hitRadius;
        const crossed = pointToSegmentDistance(
            stop.point[0],
            stop.point[1],
            previous.x,
            previous.y,
            x,
            y
        ) <= hitRadius;
        if (!directHit && !crossed) continue;

        const stopKey = `${round(stop.point[0])}:${round(stop.point[1])}`;
        const triggerKey = `${person.id}:${stopKey}`;
        const lastPlayedAt = pulseStopCooldownByKey.get(triggerKey) || -Infinity;
        if (now - lastPlayedAt < STOP_HIT_COOLDOWN_MS) continue;

        const waiting = pendingIntersectionMeetings.get(stopKey);
        if (!waiting || waiting.expiresAt <= now) {
            const waitMs = constrain(
                random(INTERSECTION_WAIT_MIN_MS, INTERSECTION_WAIT_MAX_MS) * (person.waitMultiplier || 1),
                INTERSECTION_WAIT_MIN_MS,
                INTERSECTION_WAIT_MAX_MS * 2.2
            );
            pulse.pausedUntil = now + waitMs;
            pulse.waitingStopKey = stopKey;
            pendingIntersectionMeetings.set(stopKey, {
                stopKey,
                lineId: line.id,
                personId: person.id,
                expiresAt: now + waitMs,
                note: stop.note || random(STOP_NOTE_POOL),
                closeness: person.closeness,
                point: [stop.point[0], stop.point[1]]
            });
            pulseStopCooldownByKey.set(triggerKey, now);
            continue;
        }

        if (waiting.personId === person.id || waiting.lineId === line.id) {
            continue;
        }

        const firstPulse = getPulseState(waiting.personId);
        firstPulse.pausedUntil = now + INTERSECTION_RELEASE_MS;
        firstPulse.waitingStopKey = null;
        pulse.pausedUntil = now + INTERSECTION_RELEASE_MS;
        pulse.waitingStopKey = null;

        const activationChance = getMeetingActivationChanceForPair(waiting.personId, person.id);
        if (random() > activationChance) {
            const firstTriggerKeyMiss = `${waiting.personId}:${stopKey}`;
            pulseStopCooldownByKey.set(firstTriggerKeyMiss, now);
            pulseStopCooldownByKey.set(triggerKey, now);
            pendingIntersectionMeetings.delete(stopKey);
            continue;
        }

        const combinedCloseness = floor((waiting.closeness + person.closeness) / 2);
        playStopNote(waiting.note, combinedCloseness);
        lineGlowUntil.set(waiting.lineId, now + 1000);
        lineGlowUntil.set(line.id, now + 1000);
        intersectionBursts.push({
            x: stop.point[0],
            y: stop.point[1],
            startedAt: now,
            durationMs: 900,
            maxRadius: 24 + combinedCloseness * 4.5
        });

        const firstTriggerKey = `${waiting.personId}:${stopKey}`;
        pulseStopCooldownByKey.set(firstTriggerKey, now);
        pulseStopCooldownByKey.set(triggerKey, now);
        pendingIntersectionMeetings.delete(stopKey);
    }

    lastPulsePositionByPerson.set(person.id, { x, y });
}

function cleanupPendingIntersectionMeetings(now) {
    for (const [stopKey, waiting] of pendingIntersectionMeetings.entries()) {
        if (waiting.expiresAt > now) continue;

        const firstPulse = getPulseState(waiting.personId);
        if (firstPulse && firstPulse.waitingStopKey === stopKey) {
            firstPulse.waitingStopKey = null;
        }
        pendingIntersectionMeetings.delete(stopKey);
    }
}

function launchEchoPulse(targetLineId, stop, sourcePerson, sourceLineId) {
    const targetPerson = findPersonByLineId(targetLineId);
    if (!targetPerson || !targetPerson.path || targetPerson.path.length < 2) return;

    const targetT = findNearestPathT(targetPerson.path, stop.point[0], stop.point[1]);
    const startT = targetT <= 0.5 ? 0 : 1;
    const direction = startT <= targetT ? 1 : -1;
    const distanceT = abs(targetT - startT);
    const travelMs = mapValue(distanceT, 0, 1, 220, 1100);

    echoPulses.push({
        personId: targetPerson.id,
        lineId: targetLineId,
        sourceLineId,
        stopPoint: stop.point,
        targetT,
        startT,
        t: startT,
        direction,
        startedAt: millis(),
        durationMs: travelMs,
        closeness: floor((sourcePerson.closeness + targetPerson.closeness) / 2),
        note: stop.note || random(STOP_NOTE_POOL),
        arrived: false
    });
}

function drawEchoPulses() {
    const now = millis();
    const active = [];

    for (const echo of echoPulses) {
        const person = people.find(entry => entry.id === echo.personId);
        if (!person || !person.path || person.path.length < 2) continue;

        const elapsed = now - echo.startedAt;
        const progress = constrain(elapsed / echo.durationMs, 0, 1);
        echo.t = lerp(echo.startT, echo.targetT, progress);
        const sample = samplePointOnPath(person.path, echo.t);
        if (!sample) continue;

        push();
        noStroke();
        const size = 8 + echo.closeness * 2.4;
        fill(255, 180, 70, 160);
        circle(sample.x, sample.y, size);
        pop();

        if (!echo.arrived && progress >= 1 - EPSILON) {
            echo.arrived = true;
            lineGlowUntil.set(echo.lineId, now + 950);
            lineGlowUntil.set(echo.sourceLineId, now + 950);
            playStopNote(echo.note, echo.closeness);
            intersectionBursts.push({
                x: echo.stopPoint[0],
                y: echo.stopPoint[1],
                startedAt: now,
                durationMs: 700,
                maxRadius: 20 + echo.closeness * 3.5
            });
        }

        if (progress < 1) active.push(echo);
    }

    echoPulses = active;
}

function drawIntersectionBursts() {
    const now = millis();
    const active = [];

    for (const burst of intersectionBursts) {
        const age = now - burst.startedAt;
        const progress = age / burst.durationMs;
        if (progress >= 1) continue;

        const radius = lerp(8, burst.maxRadius, progress);
        const alpha = lerp(180, 0, progress);
        push();
        noFill();
        stroke(255, 210, 90, alpha);
        strokeWeight(2.2);
        circle(burst.x, burst.y, radius);
        pop();

        active.push(burst);
    }

    intersectionBursts = active;
}

function playStopNote(note, closeness = 3) {
    if (!polySynth) return;
    try {
        ensureAudioReady();
        const velocity = STOP_NOTE_VOLUME * mapValue(closeness, 1, 5, 0.6, 1.4);
        const duration = STOP_NOTE_DURATION * mapValue(closeness, 1, 5, 0.85, 1.2);
        polySynth.play(note, velocity, 0, duration);
    } catch (err) {
        // keep render loop alive even if audio fails intermittently
    }
}

function pointToSegmentDistance(px, py, x1, y1, x2, y2) {
    const dx = x2 - x1;
    const dy = y2 - y1;
    const lenSq = dx * dx + dy * dy;
    if (lenSq < EPSILON) return dist(px, py, x1, y1);
    let t = ((px - x1) * dx + (py - y1) * dy) / lenSq;
    t = constrain(t, 0, 1);
    const projX = x1 + t * dx;
    const projY = y1 + t * dy;
    return dist(px, py, projX, projY);
}

function samplePointOnPath(pathPoints, t) {
    if (!pathPoints || pathPoints.length < 2) return null;
    const clampedT = constrain(t, 0, 1);
    let total = 0;
    const lens = [];
    for (let i = 0; i < pathPoints.length - 1; i++) {
        const a = pathPoints[i];
        const b = pathPoints[i + 1];
        const len = dist(a[0], a[1], b[0], b[1]);
        lens.push(len);
        total += len;
    }
    if (total <= EPSILON) {
        const a = pathPoints[0];
        const b = pathPoints[1];
        return {
            x: a[0],
            y: a[1],
            angle: atan2(b[1] - a[1], b[0] - a[0])
        };
    }

    let target = total * clampedT;
    for (let i = 0; i < lens.length; i++) {
        if (target > lens[i]) {
            target -= lens[i];
            continue;
        }
        const a = pathPoints[i];
        const b = pathPoints[i + 1];
        const ratio = lens[i] <= EPSILON ? 0 : target / lens[i];
        return {
            x: lerp(a[0], b[0], ratio),
            y: lerp(a[1], b[1], ratio),
            angle: atan2(b[1] - a[1], b[0] - a[0])
        };
    }
    const last = pathPoints[pathPoints.length - 1];
    const prev = pathPoints[pathPoints.length - 2];
    return {
        x: last[0],
        y: last[1],
        angle: atan2(last[1] - prev[1], last[0] - prev[0])
    };
}

function syncPersonPathFromLine(person) {
    if (!person) return;
    const line = findLineByPersonId(person.id);
    person.path = line ? line.points.map(point => [point[0], point[1]]) : [];
}

function pickRouteSpecForPerson(person) {
    const pool = buildRouteFamilySpecs();
    if (person.fate >= 4) {
        const centerHeavy = pool.filter(spec => spec.secondaryHub || random() < 0.6);
        if (centerHeavy.length) return random(centerHeavy);
    }
    return random(pool);
}

function findStationByName(name) {
    return controlStations.find(station => station.name === name) || null;
}

function getPrimaryLine() {
    const primaryPerson = people.find(person => person.isPrimary);
    if (!primaryPerson) return null;
    return findLineByPersonId(primaryPerson.id) || null;
}

function getStationAnchorKeyByName(stationName) {
    const anchor = stationAnchorByName.get(stationName);
    if (!anchor) return null;
    return stopKeyFromPoint(anchor[0], anchor[1]);
}

function getStationNameForAnchorKey(key) {
    for (const [stationName, anchor] of stationAnchorByName.entries()) {
        if (stopKeyFromPoint(anchor[0], anchor[1]) === key) return stationName;
    }
    return '';
}

function pickStationAnchorFromPrimary(stationName) {
    const primaryLine = getPrimaryLine();
    if (!primaryLine || !primaryLine.points || primaryLine.points.length < 2) return null;
    const stationIndex = max(0, controlStations.findIndex(station => station.name === stationName));
    const stationCount = max(1, controlStations.length);
    const ratio = (stationIndex + 1) / (stationCount + 1);
    const pointIndex = constrain(round((primaryLine.points.length - 1) * ratio), 1, primaryLine.points.length - 2);
    const p = primaryLine.points[pointIndex];
    if (!p) return null;
    return [p[0], p[1]];
}

function getOrCreateStationAnchor(stationName) {
    const cached = stationAnchorByName.get(stationName);
    if (cached) return cached;
    const anchor = pickStationAnchorFromPrimary(stationName);
    if (!anchor) return null;
    stationAnchorByName.set(stationName, anchor);
    return anchor;
}

function lineHasPoint(line, point) {
    if (!line || !line.points || !point) return false;
    return line.points.some(p => pointsEqual(p, point));
}

function insertPointIntoLineNearestSegment(line, point) {
    if (!line || !line.points || line.points.length < 2 || !point) return false;
    if (lineHasPoint(line, point)) return false;

    let bestIdx = -1;
    let bestDist = Infinity;
    for (let i = 0; i < line.points.length - 1; i++) {
        const a = line.points[i];
        const b = line.points[i + 1];
        const d = pointToSegmentDistance(point[0], point[1], a[0], a[1], b[0], b[1]);
        if (d < bestDist) {
            bestDist = d;
            bestIdx = i;
        }
    }
    if (bestIdx < 0) return false;

    const before = line.points[bestIdx];
    const after = line.points[bestIdx + 1];
    if (pointsEqual(before, point) || pointsEqual(after, point)) return false;

    line.points.splice(bestIdx + 1, 0, [point[0], point[1]]);
    return true;
}

function enforceStationAnchorsForLine(person, line) {
    if (!person || !line || !Array.isArray(person.stations) || !person.stations.length) return false;
    let changed = false;
    for (const stationName of person.stations) {
        const anchor = getOrCreateStationAnchor(stationName);
        if (!anchor) continue;
        if (insertPointIntoLineNearestSegment(line, anchor)) changed = true;
    }
    return changed;
}

function enforceStationAnchorsForAllLines() {
    let changed = false;
    for (const person of people) {
        const line = findLineByPersonId(person.id);
        if (!line) continue;
        if (enforceStationAnchorsForLine(person, line)) {
            syncPersonPathFromLine(person);
            changed = true;
        }
    }
    if (changed) addStops();
}

function appendStationAnchorStops(stopMap) {
    for (const station of controlStations) {
        const anchor = getOrCreateStationAnchor(station.name);
        if (!anchor) continue;
        const lineIds = [];
        for (const personId of station.people || []) {
            const person = people.find(entry => entry.id === personId);
            if (!person) continue;
            const line = findLineByPersonId(person.id);
            if (!line) continue;
            lineIds.push(line.id);
        }
        if (lineIds.length < 2) continue;

        const key = stopKeyFromPoint(anchor[0], anchor[1]);
        let stop = stopMap.get(key);
        if (!stop) {
            stop = { point: [anchor[0], anchor[1]], lines: new Set() };
            stopMap.set(key, stop);
        }
        for (const lineId of lineIds) stop.lines.add(lineId);

        if (!intersectionNamesByKey.has(key)) {
            intersectionNamesByKey.set(key, station.name);
        }
    }
}

function findLineByPersonId(personId) {
    return lines.find(line => line.personId === personId) || null;
}

function findPersonByLineId(lineId) {
    return people.find(person => {
        const line = findLineByPersonId(person.id);
        return line && line.id === lineId;
    }) || null;
}

function getFateProfile(fateValue) {
    const f = constrain(round(fateValue), 1, 5);
    if (f === 1) {
        return {
            centralTargetIntersections: 0,
            centralStopsEnabled: false,
            fateMode: 'none',
            centralMeetingChance: 0.15,
            sideMeetingChance: 0.1,
            routeIntersectionChance: 0.4,
            waitMultiplier: 0.9
        };
    }
    if (f === 2) {
        return {
            centralTargetIntersections: 1,
            centralStopsEnabled: false, // crossing can happen, but no stop node
            fateMode: 'crossNoStop',
            centralMeetingChance: 0.3,
            sideMeetingChance: 0.2,
            routeIntersectionChance: 0.4,
            waitMultiplier: 1.0
        };
    }
    if (f === 3) {
        return {
            centralTargetIntersections: 1,
            centralStopsEnabled: true,
            fateMode: 'stopCount',
            centralMeetingChance: 0.5,
            sideMeetingChance: 0.35,
            routeIntersectionChance: 0.4,
            waitMultiplier: 1.1
        };
    }
    if (f === 4) {
        return {
            centralTargetIntersections: 2,
            centralStopsEnabled: true,
            fateMode: 'stopCount',
            centralMeetingChance: 0.72,
            sideMeetingChance: 0.5,
            routeIntersectionChance: 0.4,
            waitMultiplier: 1.2
        };
    }
    return {
        centralTargetIntersections: 3,
        centralStopsEnabled: true,
        fateMode: 'stopCount',
        centralMeetingChance: 0.9,
        sideMeetingChance: 0.65,
        routeIntersectionChance: 0.4,
        waitMultiplier: 1.55 // longer wait time
    };
}

function getPrimaryLineId() {
    const primaryPerson = people.find(person => person.isPrimary);
    if (!primaryPerson) return null;
    const primaryLine = findLineByPersonId(primaryPerson.id);
    return primaryLine ? primaryLine.id : null;
}

function getCentralIntersectionStatsForLine(line) {
    const primaryLineId = getPrimaryLineId();
    if (primaryLineId === null || line.id === primaryLineId) return { rawCount: 0, stopCount: 0 };
    const primaryLine = lines.find(entry => entry.id === primaryLineId);
    if (!primaryLine) return { rawCount: 0, stopCount: 0 };
    return countIntersectionsBetweenLines(line, primaryLine);
}

function countIntersectionsBetweenLines(lineA, lineB) {
    if (!lineA || !lineB || !lineA.points || !lineB.points) {
        return { rawCount: 0, stopCount: 0 };
    }
    if (lineA.points.length < 2 || lineB.points.length < 2) {
        return { rawCount: 0, stopCount: 0 };
    }

    const rawKeys = new Set();
    const stopKeys = new Set();

    const addRawPoint = (point) => {
        rawKeys.add(stopKeyFromPoint(point[0], point[1]));
    };
    const addStopPoint = (point) => {
        const key = stopKeyFromPoint(point[0], point[1]);
        rawKeys.add(key);
        stopKeys.add(key);
    };

    for (const pA of lineA.points) {
        for (const pB of lineB.points) {
            if (!pointsEqual(pA, pB)) continue;
            addStopPoint(pA);
        }
    }

    for (let i = 0; i < lineA.points.length - 1; i++) {
        const a1 = lineA.points[i];
        const a2 = lineA.points[i + 1];
        const segA = makeSegment(a1, a2, lineA.id);

        for (let j = 0; j < lineB.points.length - 1; j++) {
            const b1 = lineB.points[j];
            const b2 = lineB.points[j + 1];
            const segB = makeSegment(b1, b2, lineB.id);

            const overlap = collinearAxisOverlap(a1, a2, b1, b2);
            if (overlap) {
                addStopPoint(overlap[0]);
                addStopPoint(overlap[1]);
                continue;
            }

            const hit = segmentIntersectionInclusive(a1, a2, b1, b2);
            if (!hit) continue;
            addRawPoint(hit);

            if (!pointOnGridVertex(hit)) continue;
            if (isDiagonalKind(segA.kind) && isDiagonalKind(segB.kind)) continue;
            const angle = segmentAngleDegrees(segA, segB);
            const angleIs45 = abs(angle - 45) < 0.2;
            const angleIs90 = abs(angle - 90) < 0.2;
            if (!angleIs45 && !angleIs90) continue;

            addStopPoint(hit);
        }
    }
    return {
        rawCount: rawKeys.size,
        stopCount: stopKeys.size
    };
}

function getFateFitScore(profile, stats) {
    if (!profile) return Infinity;
    const safeStats = stats || { rawCount: 0, stopCount: 0 };

    if (profile.fateMode === 'none') {
        return safeStats.rawCount === 0 ? 0 : safeStats.rawCount * 25 + safeStats.stopCount * 10;
    }

    if (profile.fateMode === 'crossNoStop') {
        if (safeStats.rawCount <= 0) return 120;
        if (safeStats.stopCount > 0) return safeStats.stopCount * 40 + abs(safeStats.rawCount - 1) * 2;
        return abs(safeStats.rawCount - 1);
    }

    // stopCount mode for fate 3/4/5
    const target = profile.centralTargetIntersections;
    return abs(safeStats.stopCount - target) * 12 + (safeStats.rawCount <= 0 ? 8 : 0);
}

function getMeetingActivationChanceForPair(firstPersonId, secondPersonId) {
    const primaryPerson = people.find(person => person.isPrimary);
    if (!primaryPerson) return 1;
    const primaryId = primaryPerson.id;

    const otherId = firstPersonId === primaryId ? secondPersonId : (secondPersonId === primaryId ? firstPersonId : null);
    if (otherId === null) {
        // non-user pair: keep current behavior fully active
        return 1;
    }

    const otherPerson = people.find(person => person.id === otherId);
    if (!otherPerson) return 1;
    return constrain(otherPerson.centralMeetingChance || 0, 0, 1);
}

function rerouteLineForFateProfile(person, line) {
    if (!line) return;
    if (person.isPrimary) {
        line.run();
        return;
    }

    const profile = getFateProfile(person.fate);
    let bestScore = Infinity;
    let bestPoints = null;

    for (let i = 0; i < FATE_ROUTE_MAX_TRIES; i++) {
        line.run();
        if (!line.points || line.points.length < 2) continue;
        const stats = getCentralIntersectionStatsForLine(line);
        const score = getFateFitScore(profile, stats);
        if (score < bestScore) {
            bestScore = score;
            bestPoints = line.points.map(point => [point[0], point[1]]);
        }
        if (score === 0) break;
    }

    if (bestPoints && bestPoints.length >= 2) {
        line.points = bestPoints;
    }
}

function shouldCreateStopForPair(lineAId, lineBId) {
    const primaryLineId = getPrimaryLineId();
    if (primaryLineId === null) return true;

    const otherLineId = lineAId === primaryLineId ? lineBId : (lineBId === primaryLineId ? lineAId : null);
    if (otherLineId === null) return true;
    const otherPerson = findPersonByLineId(otherLineId);
    if (!otherPerson) return true;
    return !!otherPerson.centralStopsEnabled;
}

function findNearestPathT(pathPoints, px, py) {
    if (!pathPoints || pathPoints.length < 2) return 0;

    let totalLen = 0;
    const lens = [];
    for (let i = 0; i < pathPoints.length - 1; i++) {
        const a = pathPoints[i];
        const b = pathPoints[i + 1];
        const len = dist(a[0], a[1], b[0], b[1]);
        lens.push(len);
        totalLen += len;
    }
    if (totalLen <= EPSILON) return 0;

    let bestDist = Infinity;
    let bestAlong = 0;
    let prefix = 0;
    for (let i = 0; i < pathPoints.length - 1; i++) {
        const a = pathPoints[i];
        const b = pathPoints[i + 1];
        const segLen = lens[i];
        if (segLen <= EPSILON) continue;

        const dx = b[0] - a[0];
        const dy = b[1] - a[1];
        const tSeg = constrain(((px - a[0]) * dx + (py - a[1]) * dy) / (segLen * segLen), 0, 1);
        const projX = a[0] + dx * tSeg;
        const projY = a[1] + dy * tSeg;
        const d = dist(px, py, projX, projY);
        if (d < bestDist) {
            bestDist = d;
            bestAlong = prefix + segLen * tSeg;
        }
        prefix += segLen;
    }

    return constrain(bestAlong / totalLen, 0, 1);
}

function refreshAnimationLoop() {
    if (animationTimer) {
        clearInterval(animationTimer);
        animationTimer = null;
    }

    if (!people.length) return;
    const delay = 48;
    animationTimer = setInterval(() => {
        redraw();
    }, delay);
}

function enableSoundOnFirstGesture() {
    const unlockAudio = () => {
        try {
            userStartAudio();
            const ctx = typeof getAudioContext === 'function' ? getAudioContext() : null;
            if (ctx && ctx.state !== 'running') ctx.resume();
            if (!audioUnlocked) {
                audioUnlocked = true;
                // quick audible confirmation that audio is alive
                setTimeout(() => {
                    playStopNote('A5', 5);
                }, 40);
            }
        } catch (err) {
            // Ignore unlock errors; subsequent gestures will retry.
        }
    };
    window.addEventListener('pointerdown', unlockAudio);
    window.addEventListener('keydown', unlockAudio);
}

function mousePressed() {
    ensureAudioReady();
    const hit = findStopAtPosition(mouseX, mouseY);
    if (!hit) return;

    const currentName = hit.name || '';
    const input = window.prompt('Name this intersection:', currentName);
    if (input === null) return;
    const trimmed = input.trim();
    const key = stopKeyFromPoint(hit.point[0], hit.point[1]);
    if (!trimmed) {
        intersectionNamesByKey.delete(key);
        hit.name = '';
    } else {
        intersectionNamesByKey.set(key, trimmed);
        hit.name = trimmed;
    }
    redraw();
}

function touchStarted() {
    ensureAudioReady();
}

function ensureAudioReady() {
    try {
        if (typeof userStartAudio === 'function') userStartAudio();
        const ctx = typeof getAudioContext === 'function' ? getAudioContext() : null;
        if (ctx && ctx.state !== 'running') ctx.resume();
    } catch (err) {
        // browser may still block until next explicit gesture
    }
}

function stopKeyFromPoint(x, y) {
    return `${round(x)}:${round(y)}`;
}

function findStopAtPosition(x, y) {
    const hitRadius = 12;
    for (const stop of stops) {
        if (dist(x, y, stop.point[0], stop.point[1]) <= hitRadius) return stop;
    }
    return null;
}

function getRandomMutedColor() {
    return random(PANEL_COLOR_PALETTE);
}

function mapValue(value, inMin, inMax, outMin, outMax) {
    if (abs(inMax - inMin) < EPSILON) return outMin;
    return ((value - inMin) * (outMax - outMin)) / (inMax - inMin) + outMin;
}

function drawGridVertices() {
    noStroke();
    fill(180, 150, 110);

    for (const p of gridPoints) {
        circle(p.x, p.y, 4);
    }
}

function drawCentralBox() {
    noFill();
    stroke(120, 95, 70, 140);
    strokeWeight(1.5);
    rectMode(CORNERS);
    rect(central.minX, central.minY, central.maxX, central.maxY);
}

function segmentIntersectionStrict(p1, p2, p3, p4) {
    const x1 = p1[0], y1 = p1[1];
    const x2 = p2[0], y2 = p2[1];
    const x3 = p3[0], y3 = p3[1];
    const x4 = p4[0], y4 = p4[1];

    const denom = (x1 - x2) * (y3 - y4) - (y1 - y2) * (x3 - x4);
    if (abs(denom) < EPSILON) return null;

    const t = ((x1 - x3) * (y3 - y4) - (y1 - y3) * (x3 - x4)) / denom;
    const u = ((x1 - x3) * (y1 - y2) - (y1 - y3) * (x1 - x2)) / denom;
    if (t <= EPSILON || t >= 1 - EPSILON || u <= EPSILON || u >= 1 - EPSILON) return null;

    return [
        x1 + t * (x2 - x1),
        y1 + t * (y2 - y1)
    ];
}

function addStopNode(point, lineAId, lineBId, stopMap) {
    const key = `${round(point[0])}:${round(point[1])}`;
    let stop = stopMap.get(key);
    if (!stop) {
        stop = {
            point: [point[0], point[1]],
            lines: new Set()
        };
        stopMap.set(key, stop);
    }
    stop.lines.add(lineAId);
    stop.lines.add(lineBId);
}

function addStops() {
    stops = [];
    joins = [];
    pulseStopCooldownByKey = new Map();
    lastPulsePositionByPerson = new Map();
    pulseStateByPerson = new Map();
    echoPulses = [];
    intersectionBursts = [];
    lineGlowUntil = new Map();
    pendingIntersectionMeetings = new Map();
    stationAnchorByName = new Map();
    const stopMap = new Map();

    for (let a = 0; a < lines.length; a++) {
        for (let b = a + 1; b < lines.length; b++) {
            const lineA = lines[a];
            const lineB = lines[b];
            const lineAId = lineA.id;
            const lineBId = lineB.id;
            if (!shouldCreateStopForPair(lineAId, lineBId)) continue;

            // Interchange at exact shared vertices (including terminals).
            for (const pA of lineA.points) {
                for (const pB of lineB.points) {
                    if (!pointsEqual(pA, pB)) continue;
                    addStopNode(pA, lineAId, lineBId, stopMap);
                }
            }

            for (let i = 0; i < lineA.points.length - 1; i++) {
                const a1 = lineA.points[i];
                const a2 = lineA.points[i + 1];
                const segA = makeSegment(a1, a2, a);

                for (let j = 0; j < lineB.points.length - 1; j++) {
                    const b1 = lineB.points[j];
                    const b2 = lineB.points[j + 1];
                    const segB = makeSegment(b1, b2, b);

                    const overlap = collinearAxisOverlap(a1, a2, b1, b2);
                    if (overlap) {
                        addStopNode(overlap[0], lineAId, lineBId, stopMap);
                        addStopNode(overlap[1], lineAId, lineBId, stopMap);
                        continue;
                    }

                    const hit = segmentIntersectionInclusive(a1, a2, b1, b2);
                    if (!hit) continue;
                    if (!pointOnGridVertex(hit)) continue;
                    if (isDiagonalKind(segA.kind) && isDiagonalKind(segB.kind)) continue;

                    const angle = segmentAngleDegrees(segA, segB);
                    const angleIs45 = abs(angle - 45) < 0.2;
                    const angleIs90 = abs(angle - 90) < 0.2;
                    if (!angleIs45 && !angleIs90) continue;

                    addStopNode(hit, lineAId, lineBId, stopMap);
                }
            }
        }
    }

    stops = Array.from(stopMap.values())
        .filter(stop => stop.lines.size >= 2)
        .map(stop => ({
            point: stop.point,
            lines: Array.from(stop.lines),
            note: random(STOP_NOTE_POOL),
            name: intersectionNamesByKey.get(stopKeyFromPoint(stop.point[0], stop.point[1])) || ''
        }));

    for (let i = 0; i < stops.length; i++) {
        for (let j = i + 1; j < stops.length; j++) {
            const s1 = stops[i].point;
            const s2 = stops[j].point;
            const d = dist(s1[0], s1[1], s2[0], s2[1]);

            if (abs(d - distLength) < 5) {
                joins.push([s1, s2]);
            }
        }
    }
}

function drawStops() {
    if (!stopSmileySvg) return;

    const stopSize = 10;
    const svgAspect = stopSmileySvg.width > 0 && stopSmileySvg.height > 0
        ? stopSmileySvg.width / stopSmileySvg.height
        : 1;
    const drawWidth = svgAspect >= 1 ? stopSize : stopSize * svgAspect;
    const drawHeight = svgAspect >= 1 ? stopSize / svgAspect : stopSize;

    for (const s of stops) {
        push();
        imageMode(CENTER);
        image(stopSmileySvg, s.point[0], s.point[1], drawWidth, drawHeight);
        if (s.name) {
            noStroke();
            fill(38, 34, 29, 210);
            textAlign(LEFT, CENTER);
            textSize(13);
            text(s.name, s.point[0] + 10, s.point[1] - 12);
        }
        pop();
    }
}

function drawStartPoints() {
    strokeWeight(3);
    for (const l of lines) {
        // Start terminal
        const start = l.points[0];
        fill(255);
        stroke(l.lineColor[0], l.lineColor[1], l.lineColor[2]);
        circle(start[0], start[1], 18);

        // End terminal
        const end = l.points[l.points.length - 1];
        circle(end[0], end[1], 18);
    }
}

function isInCentralBox(x,y) {
    return (
        x >= central.minX &&
        x <= central.maxX &&
        y >= central.minY &&
        y <= central.maxY
    ); 
}

function isOutsideCentralBuffer(x, y, steps) {
    const margin = distLength * steps;
    return (
        x < central.minX - margin ||
        x > central.maxX + margin ||
        y < central.minY - margin ||
        y > central.maxY + margin
    );
}

function directionTowardCentral(x, y, targetHub = null) {
    const cx = targetHub ? targetHub.x : (gridBounds.minX + gridBounds.maxX) / 2;
    const cy = targetHub ? targetHub.y : (gridBounds.minY + gridBounds.maxY) / 2;

    const dx = cx - x; //checks how far the current point is from the center
    const dy = cy - y;

    if (abs(dx) > abs(dy) * 1.5) {
        return dx > 0 ? 3 : 7; //center is to the right: go right (3), otherwise go left (7)
    }

    if (abs(dy) > abs(dx) * 1.5) {
        return dy > 0 ? 5 : 1; //center is above: go up (5), otherwise go down (1)
    }

    if (dx > 0 && dy > 0) return 4;
    if (dx > 0 && dy < 0) return 2;
    if (dx < 0 && dy > 0) return 6;
    if (dx < 0 && dy < 0) return 8;

    return floor(random(1, 9)); //backup: if the point is exactly at the center, there is no clear direction, so it picks a random direction from 1 to 8
}

function directionAwayFromCentral(x, y) {
    const cx = (gridBounds.minX + gridBounds.maxX) / 2;
    const cy = (gridBounds.minY + gridBounds.maxY) / 2;
    return directionTowardCentral(cx, cy, { x, y });
}

function wrapDirection(d) {
    if (d < 1) return 8;
    if (d > 8) return 1;
    return d;
}

function oppositeDirection(d) {
    return wrapDirection(d + 4);
}

function circularDiff(a, b) {
    let d = b - a;
    while (d > 4) d -= 8;
    while (d < -4) d += 8;
    return d;
}

function absCircularDiff(a, b) {
    return abs(circularDiff(a, b));
}

function steerDirectionToward(currentDir, targetDir, maxStep = 1) {
    const d = circularDiff(currentDir, targetDir);
    if (abs(d) <= maxStep) return wrapDirection(currentDir + d);
    return wrapDirection(currentDir + (d > 0 ? maxStep : -maxStep));
}

function pointKeyXY(x, y) {
    return `${round(x)}:${round(y)}`;
}

function isNearRecentPoint(points, nextPoint, lookbackSteps, radius) {
    const start = max(0, points.length - lookbackSteps);
    const end = max(0, points.length - 2);
    for (let i = start; i <= end; i++) {
        if (dist(points[i][0], points[i][1], nextPoint[0], nextPoint[1]) <= radius) {
            return true;
        }
    }
    return false;
}

function createsSmallLoop(points, nextPoint) {
    const n = points.length;
    if (n >= 3 && pointsEqual(nextPoint, points[n - 3])) return true;
    if (n >= 4 && pointsEqual(nextPoint, points[n - 4])) return true;
    return false;
}

function isInHubArea(x, y, hub) {
    if (!hub) return isInCentralBox(x, y);
    return dist(x, y, hub.x, hub.y) <= distLength * HUB_REACH_RADIUS;
}

function getLinePhase(lineObj) {
    if (!lineObj.touchedCentralBox) return 'toCenter';
    if (!lineObj.exitedCentralBoxAfterTouch) return 'throughCenter';
    return 'toEnd';
}

function wouldCreateTurnOverflow(flags, nextTurnFlag) {
    const recent = flags.slice(-TURN_WINDOW + 1);
    recent.push(nextTurnFlag);
    return recent.filter(Boolean).length > MAX_TURNS_IN_WINDOW;
}

function wouldCreateStaircase(turnSteps, nextStep) {
    if (nextStep === 0 || turnSteps.length < 2) return false;
    const a = turnSteps[turnSteps.length - 2];
    const b = turnSteps[turnSteps.length - 1];
    return a !== 0 && b !== 0 && a === -b && b === -nextStep;
}

function wouldRepeatZigzag(turnSteps, nextStep) {
    if (nextStep === 0) return false;
    let last = 0;
    let prev = 0;

    for (let i = turnSteps.length - 1; i >= 0; i--) {
        if (turnSteps[i] === 0) continue;
        if (last === 0) {
            last = turnSteps[i];
        } else {
            prev = turnSteps[i];
            break;
        }
    }

    if (prev === 0 || last === 0) return false;
    return prev === -last && nextStep === prev;
}

function wouldCreateAlternatingStepPattern(stepDirHistory, nextDir) {
    // Reject ABAB local stepping, e.g. right -> down-right -> right -> down-right
    if (stepDirHistory.length < 3) return false;
    const a = stepDirHistory[stepDirHistory.length - 3];
    const b = stepDirHistory[stepDirHistory.length - 2];
    const c = stepDirHistory[stepDirHistory.length - 1];
    const d = nextDir;
    return a === c && b === d && a !== b;
}

function canAcceptTurn(lineObj, nextDir, turnStep) {
    if (turnStep === 0) return true;

    if (!lineObj.canTurnNow()) return false;

    if (wouldCreateTurnOverflow(lineObj.recentTurnFlags, true)) return false;
    if (wouldCreateStaircase(lineObj.recentTurnSteps, turnStep)) return false;
    if (wouldRepeatZigzag(lineObj.recentTurnSteps, turnStep)) return false;
    if (wouldCreateAlternatingStepPattern(lineObj.stepDirHistory, nextDir)) return false;

    return true;
}

function weightedPickByScore(items) {
    const maxScore = max(...items.map(i => i.score));
    const weighted = items.map(i => ({ ...i, w: max(0.1, i.score - maxScore + 6) }));
    const total = weighted.reduce((sum, i) => sum + i.w, 0);
    let r = random(total);
    for (const i of weighted) {
        r -= i.w;
        if (r <= 0) return i;
    }
    return weighted[0];
}

function shuffleArray(arr) {
    for (let i = arr.length - 1; i > 0; i--) {
        const j = floor(random(i + 1));
        const t = arr[i];
        arr[i] = arr[j];
        arr[j] = t;
    }
    return arr;
}

function normalizeHexColor(hex) {
    if (!hex) return '#000000';
    const cleaned = `${hex}`.replace('#', '').trim();
    if (cleaned.length !== 6) return '#000000';
    return `#${cleaned.toUpperCase()}`;
}

function hexToRgbArray(hex) {
    const normalized = normalizeHexColor(hex).slice(1);
    return [
        parseInt(normalized.slice(0, 2), 16),
        parseInt(normalized.slice(2, 4), 16),
        parseInt(normalized.slice(4, 6), 16)
    ];
}

function rgbArrayToCssHex(rgb) {
    const safe = Array.isArray(rgb) ? rgb : [0, 0, 0];
    const hex = safe
        .slice(0, 3)
        .map(value => constrain(round(value), 0, 255).toString(16).padStart(2, '0').toUpperCase())
        .join('');
    return `#${hex}`;
}

function mergeNearbyTurns(points) {
    if (points.length < 5) return points;
    const out = [points[0]];
    let i = 1;

    while (i < points.length - 2) {
        const p0 = out[out.length - 1];
        const p1 = points[i];
        const p2 = points[i + 1];
        const p3 = points[i + 2];

        const d1 = directionFromPoints(p0, p1);
        const d2 = directionFromPoints(p1, p2);
        const d3 = directionFromPoints(p2, p3);

        const microMid = dist(p1[0], p1[1], p2[0], p2[1]) <= distLength * 1.01;
        const repeatedOuter = d1 === d3 && d1 !== d2;

        if (microMid && repeatedOuter) {
            out.push(p3);
            i += 3;
            continue;
        }

        out.push(p1);
        i += 1;
    }

    while (i < points.length) {
        out.push(points[i]);
        i++;
    }

    return out;
}

function directionFromPoints(a, b) {
    const dx = b[0] - a[0];
    const dy = b[1] - a[1];
    if (abs(dx) < EPSILON && dy < 0) return 1;
    if (dx > 0 && dy < 0) return 2;
    if (dx > 0 && abs(dy) < EPSILON) return 3;
    if (dx > 0 && dy > 0) return 4;
    if (abs(dx) < EPSILON && dy > 0) return 5;
    if (dx < 0 && dy > 0) return 6;
    if (dx < 0 && abs(dy) < EPSILON) return 7;
    if (dx < 0 && dy < 0) return 8;
    return 0;
}

//Fixed interchanged points
function getCentralHubPoints() {
    const cx = (gridBounds.minX + gridBounds.maxX) / 2;
    const cy = (gridBounds.minY + gridBounds.maxY) / 2;
    const s = distLength;
    const h = HUB_SPREAD_STEPS * s;

    return [
        { x: cx, y: cy },
        { x: cx - s, y: cy },
        { x: cx + s, y: cy },
        { x: cx, y: cy - s },
        { x: cx, y: cy + s },
        { x: cx - s, y: cy - s },
        { x: cx + s, y: cy - s },
        { x: cx - s, y: cy + s },
        { x: cx + s, y: cy + s },
        { x: cx - h, y: cy },
        { x: cx + h, y: cy },
        { x: cx, y: cy - h },
        { x: cx, y: cy + h }
    ];
}

function drawHubs() {
    if (!SHOW_HUB_DEBUG) return;
    const hubs = getCentralHubPoints();

    fill(0);
    noStroke();

    for (const h of hubs) {
        circle(h.x, h.y, 10);
    }
}

function buildRouteFamilySpecs() {
    const specs = [];
    const used = new Set();
    const usedHubKeys = new Set();
    const oppositeBySide = {
        W: 'E',
        E: 'W',
        N: 'S',
        S: 'N',
        SW: 'NE',
        NE: 'SW',
        NW: 'SE',
        SE: 'NW'
    };

    const makeSpec = (startSide, hub, extra = {}) => {
        const start = pickEdgeTerminal(startSide, used);
        const endSide = extra.endSide || oppositeBySide[startSide] || random(['N', 'S', 'E', 'W']);
        const end = pickEdgeTerminal(endSide, used);
        return {
            start,
            end,
            hub,
            ...extra
        };
    };

    for (let i = 0; i < FAMILY_COUNTS.westEast; i++) {
        specs.push(makeSpec('W', pickDistinctHub('horizontal', usedHubKeys)));
    }

    for (let i = 0; i < FAMILY_COUNTS.northSouth; i++) {
        specs.push(makeSpec('N', pickDistinctHub('vertical', usedHubKeys)));
    }

    for (let i = 0; i < FAMILY_COUNTS.swNe; i++) {
        specs.push(makeSpec('SW', pickDistinctHub('diagUp', usedHubKeys)));
    }

    for (let i = 0; i < FAMILY_COUNTS.nwSe; i++) {
        specs.push(makeSpec('NW', pickDistinctHub('diagDown', usedHubKeys)));
    }

    for (let i = 0; i < FAMILY_COUNTS.shortBranch; i++) {
        const sideA = random(['W', 'N', 'E', 'S']);
        const branchEnd = nextClockwiseSide(sideA);
        specs.push(makeSpec(sideA, pickDistinctHub('inner', usedHubKeys), { endSide: branchEnd }));
    }

    for (let i = 0; i < FAMILY_COUNTS.centerBox; i++) {
        specs.push(makeSpec('W', pickDistinctHub('top', usedHubKeys), { secondaryHub: pickDistinctHub('bottom', usedHubKeys) }));
    }

    return shuffleArray(specs);
}

function hubKey(h) {
    return `${round(h.x)}:${round(h.y)}`;
}

function minHubDistanceToUsed(h, usedHubKeys) {
    if (!usedHubKeys.size) return Infinity;
    let dMin = Infinity;
    for (const key of usedHubKeys) {
        const [ux, uy] = key.split(':').map(Number);
        dMin = min(dMin, dist(h.x, h.y, ux, uy));
    }
    return dMin;
}

function pickDistinctHub(mode, usedHubKeys) {
    const cx = (gridBounds.minX + gridBounds.maxX) / 2;
    const cy = (gridBounds.minY + gridBounds.maxY) / 2;

    let pool = centralHubs.slice();
    if (mode === 'horizontal') pool = pool.filter(h => abs(h.y - cy) <= distLength * 0.6);
    if (mode === 'vertical') pool = pool.filter(h => abs(h.x - cx) <= distLength * 0.6);
    if (mode === 'diagUp') pool = pool.filter(h => (h.x - cx) * (h.y - cy) < 0 || abs(h.x - cx) < EPSILON || abs(h.y - cy) < EPSILON);
    if (mode === 'diagDown') pool = pool.filter(h => (h.x - cx) * (h.y - cy) > 0 || abs(h.x - cx) < EPSILON || abs(h.y - cy) < EPSILON);
    if (mode === 'inner') pool = pool.filter(h => dist(h.x, h.y, cx, cy) <= distLength * 1.5);
    if (mode === 'top') pool = pool.filter(h => h.y <= cy + EPSILON);
    if (mode === 'bottom') pool = pool.filter(h => h.y >= cy - EPSILON);

    if (!pool.length) pool = centralHubs.slice();

    const available = pool.filter(h => !usedHubKeys.has(hubKey(h)));
    const selectionPool = available.length ? available : pool;
    selectionPool.sort((a, b) => minHubDistanceToUsed(b, usedHubKeys) - minHubDistanceToUsed(a, usedHubKeys));
    const topN = selectionPool.slice(0, min(3, selectionPool.length));
    const chosen = random(topN);
    usedHubKeys.add(hubKey(chosen));
    return chosen;
}

function nextClockwiseSide(side) {
    if (side === 'W') return 'N';
    if (side === 'N') return 'E';
    if (side === 'E') return 'S';
    return 'W';
}

function pointAxisKey(value) {
    return round(value / TERMINAL_AXIS_TOL) * TERMINAL_AXIS_TOL;
}

function pickTerminalOutsideBox(used, usedXs, usedYs) {
    const pool = gridPoints.filter(p =>
        !isInCentralBox(p.x, p.y) &&
        isOutsideCentralBuffer(p.x, p.y, TERMINAL_MIN_BOX_STEPS)
    );

    if (!pool.length) {
        const any = random(gridPoints);
        return { x: any.x, y: any.y };
    }

    const filtered = pool.filter(p =>
        !usedXs.has(pointAxisKey(p.x)) &&
        !usedYs.has(pointAxisKey(p.y))
    );

    const candidates = filtered.length ? filtered : pool;

    for (let t = 0; t < 120; t++) {
        const c = random(candidates);
        const key = `${round(c.x)}:${round(c.y)}`;
        if (used.has(key)) continue;
        const tooClose = Array.from(used).some(k => {
            const [ux, uy] = k.split(':').map(Number);
            return dist(ux, uy, c.x, c.y) < distLength * 2.5;
        });
        if (tooClose) continue;
        used.add(key);
        usedXs.add(pointAxisKey(c.x));
        usedYs.add(pointAxisKey(c.y));
        return { x: c.x, y: c.y };
    }

    const fallback = random(candidates);
    usedXs.add(pointAxisKey(fallback.x));
    usedYs.add(pointAxisKey(fallback.y));
    return { x: fallback.x, y: fallback.y };
}

function pickEdgeTerminal(side, used) {
    // Use actual sampled grid extents (not theoretical bounds) to avoid empty edge sets.
    const xs = gridPoints.map(p => p.x);
    const ys = gridPoints.map(p => p.y);
    const edgeMinX = min(xs);
    const edgeMaxX = max(xs);
    const edgeMinY = min(ys);
    const edgeMaxY = max(ys);
    const tol = EPSILON * 10;

    const candidates = gridPoints.filter(p => {
        const atW = abs(p.x - edgeMinX) < tol;
        const atE = abs(p.x - edgeMaxX) < tol;
        const atN = abs(p.y - edgeMinY) < tol;
        const atS = abs(p.y - edgeMaxY) < tol;

        if (side === 'W') return atW;
        if (side === 'E') return atE;
        if (side === 'N') return atN;
        if (side === 'S') return atS;
        if (side === 'SW') return atW || atS;
        if (side === 'SE') return atE || atS;
        if (side === 'NW') return atW || atN;
        if (side === 'NE') return atE || atN;
        return atW || atE || atN || atS;
    }).filter(p => !isInCentralBox(p.x, p.y) && isOutsideCentralBuffer(p.x, p.y, TERMINAL_MIN_BOX_STEPS));

    // Fallback: if a specific side has no candidates, use any perimeter point.
    const perimeterFallback = gridPoints.filter(p => {
        const atW = abs(p.x - edgeMinX) < tol;
        const atE = abs(p.x - edgeMaxX) < tol;
        const atN = abs(p.y - edgeMinY) < tol;
        const atS = abs(p.y - edgeMaxY) < tol;
        return (atW || atE || atN || atS) && !isInCentralBox(p.x, p.y) && isOutsideCentralBuffer(p.x, p.y, TERMINAL_MIN_BOX_STEPS);
    });

    const pool = candidates.length ? candidates : perimeterFallback;
    if (!pool.length) {
        const any = random(gridPoints);
        return { x: any.x, y: any.y };
    }

    for (let t = 0; t < 80; t++) {
        const c = random(pool);
        const key = `${round(c.x)}:${round(c.y)}`;
        if (used.has(key)) continue;
        const tooClose = Array.from(used).some(k => {
            const [ux, uy] = k.split(':').map(Number);
            return dist(ux, uy, c.x, c.y) < distLength * 2.5;
        });
        if (tooClose) continue;
        used.add(key);
        return { x: c.x, y: c.y };
    }

    const fallback = random(pool);
    return { x: fallback.x, y: fallback.y };
}

function drawRoundedPolyline(points, radius) {
    if (points.length < 2) return;

    beginShape();

    // start point
    vertex(points[0][0], points[0][1]);

    for (let i = 1; i < points.length - 1; i++) {
        const prev = points[i - 1];
        const curr = points[i];
        const next = points[i + 1];

        const v1x = prev[0] - curr[0];
        const v1y = prev[1] - curr[1];
        const v2x = next[0] - curr[0];
        const v2y = next[1] - curr[1];

        const len1 = sqrt(v1x * v1x + v1y * v1y);
        const len2 = sqrt(v2x * v2x + v2y * v2y);

        const r = min(radius, len1 / 2, len2 / 2);

        // point before the corner
        const p1x = curr[0] + (v1x / len1) * r;
        const p1y = curr[1] + (v1y / len1) * r;

        // point after the corner
        const p2x = curr[0] + (v2x / len2) * r;
        const p2y = curr[1] + (v2y / len2) * r;

        vertex(p1x, p1y);

        // curved corner
        quadraticVertex(curr[0], curr[1], p2x, p2y);
    }

    // end point
    const last = points[points.length - 1];
    vertex(last[0], last[1]);

    endShape();
}
