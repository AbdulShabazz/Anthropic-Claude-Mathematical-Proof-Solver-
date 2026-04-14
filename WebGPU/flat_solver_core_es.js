import * as coreCjs from './flat_solver_core.js';
export const {
  TokenStore,
  parseInput,
  compileProblem,
  solveFlat,
  generateLiteralBatch,
  heuristic,
  hashTokenIds,
  signatureKey,
  WGSL_MATCH_LITERAL,
} = coreCjs;
export default coreCjs;
