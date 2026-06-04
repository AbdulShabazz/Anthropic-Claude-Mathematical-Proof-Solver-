"use strict";

/**
 * @description: ANN accepts LHS/RHS theorem features (Performant revision 1)
 * 
 * @returns: Suitable rewrite Axiom (0-based index), computed internally as bitfield.
 */

function mulberry32(seed) {
  return function rand() {
    let x = seed += 0x6D2B79F5;
    x = Math.imul(x ^ (x >>> 15), x | 1);
    x ^= x + Math.imul(x ^ (x >>> 7), x | 61);
    return ((x ^ (x >>> 14)) >>> 0) / 4294967296;
  };
}

function relu(x) {
  return x > 0 ? x : 0;
}

function reluDerivative(x) {
  return x > 0 ? 1 : 0;
}

function sigmoid(x) {
  if (x >= 0) {
    const z = Math.exp(-x);
    return 1 / (1 + z);
  }

  const z = Math.exp(x);
  return z / (1 + z);
}

function requiredAddressBits(count) {
  if (!Number.isInteger(count) || count <= 1) {
    throw new Error("axiomCount must be an integer greater than 1.");
  }

  return Math.ceil(Math.log2(count));
}

function indexToBits(index, bitCount) {
  const bits = new Float32Array(bitCount);

  for (let b = 0; b < bitCount; b++) {
    bits[b] = (index >> b) & 1;
  }

  return bits;
}

function bitsToIndex(bitProbabilities, threshold = 0.5) {
  let index = 0;

  for (let b = 0; b < bitProbabilities.length; b++) {
    if (bitProbabilities[b] >= threshold) {
      index += 2 ** b;
    }
  }

  return index;
}

class AxiomAddressANN {
  constructor({
    inputSize,
    hiddenSize,
    axiomCount,
    learningRate = 0.02,
    seed = 1234
  }) {
    if (!Number.isInteger(inputSize) || inputSize <= 0) {
      throw new Error("inputSize must be a positive integer.");
    }

    if (!Number.isInteger(hiddenSize) || hiddenSize <= 0) {
      throw new Error("hiddenSize must be a positive integer.");
    }

    this.inputSize = inputSize;
    this.hiddenSize = hiddenSize;
    this.axiomCount = axiomCount;
    this.addressBits = requiredAddressBits(axiomCount);
    this.learningRate = learningRate;

    const rand = mulberry32(seed);

    this.W1 = new Float32Array(hiddenSize * inputSize);
    this.b1 = new Float32Array(hiddenSize);

    this.W2 = new Float32Array(this.addressBits * hiddenSize);
    this.b2 = new Float32Array(this.addressBits);

    const w1Scale = Math.sqrt(2 / inputSize);
    const w2Scale = Math.sqrt(2 / hiddenSize);

    for (let i = 0; i < this.W1.length; i++) {
      this.W1[i] = (rand() * 2 - 1) * w1Scale;
    }

    for (let i = 0; i < this.W2.length; i++) {
      this.W2[i] = (rand() * 2 - 1) * w2Scale;
    }

    this.rand = rand;
  }

  validateInput(t) {
    if (!Array.isArray(t) && !(t instanceof Float32Array)) {
      throw new Error("Input t must be an Array or Float32Array.");
    }

    if (t.length !== this.inputSize) {
      throw new Error(`Input t must have length ${this.inputSize}.`);
    }

    for (let i = 0; i < t.length; i++) {
      if (!Number.isFinite(t[i])) {
        throw new Error("Input t must contain only finite numbers.");
      }
    }
  }

  validateIndex(i) {
    if (!Number.isInteger(i) || i < 0 || i >= this.axiomCount) {
      throw new Error(`Axiom index must be in [0, ${this.axiomCount - 1}].`);
    }
  }

  forward(t) {
    this.validateInput(t);

    const z1 = new Float32Array(this.hiddenSize);
    const a1 = new Float32Array(this.hiddenSize);

    for (let h = 0; h < this.hiddenSize; h++) {
      let sum = this.b1[h];
      const row = h * this.inputSize;

      for (let j = 0; j < this.inputSize; j++) {
        sum += this.W1[row + j] * t[j];
      }

      z1[h] = sum;
      a1[h] = relu(sum);
    }

    const z2 = new Float32Array(this.addressBits);
    const bitProbabilities = new Float32Array(this.addressBits);

    for (let b = 0; b < this.addressBits; b++) {
      let sum = this.b2[b];
      const row = b * this.hiddenSize;

      for (let h = 0; h < this.hiddenSize; h++) {
        sum += this.W2[row + h] * a1[h];
      }

      z2[b] = sum;
      bitProbabilities[b] = sigmoid(sum);
    }

    return { z1, a1, z2, bitProbabilities };
  }

  predictAddress(t) {
    const { bitProbabilities } = this.forward(t);
    const i = bitsToIndex(bitProbabilities);

    let confidence = 1;

    for (let b = 0; b < bitProbabilities.length; b++) {
      const p = bitProbabilities[b];
      confidence *= Math.max(p, 1 - p);
    }

    return {
      i: i < this.axiomCount ? i : -1,
      rawAddress: i,
      valid: i >= 0 && i < this.axiomCount,
      confidence,
      bitProbabilities
    };
  }

  trainOne(t, expectedIndex) {
    this.validateInput(t);
    this.validateIndex(expectedIndex);

    const targetBits = indexToBits(expectedIndex, this.addressBits);
    const { z1, a1, bitProbabilities } = this.forward(t);

    const dz2 = new Float32Array(this.addressBits);

    let loss = 0;

    for (let b = 0; b < this.addressBits; b++) {
      const p = Math.min(Math.max(bitProbabilities[b], 1e-7), 1 - 1e-7);
      const y = targetBits[b];

      loss += -(y * Math.log(p) + (1 - y) * Math.log(1 - p));

      // Binary cross-entropy with sigmoid derivative.
      dz2[b] = p - y;
    }

    const oldW2 = new Float32Array(this.W2);

    for (let b = 0; b < this.addressBits; b++) {
      const row = b * this.hiddenSize;

      for (let h = 0; h < this.hiddenSize; h++) {
        this.W2[row + h] -= this.learningRate * dz2[b] * a1[h];
      }

      this.b2[b] -= this.learningRate * dz2[b];
    }

    const dz1 = new Float32Array(this.hiddenSize);

    for (let h = 0; h < this.hiddenSize; h++) {
      let grad = 0;

      for (let b = 0; b < this.addressBits; b++) {
        grad += oldW2[b * this.hiddenSize + h] * dz2[b];
      }

      dz1[h] = grad * reluDerivative(z1[h]);
    }

    for (let h = 0; h < this.hiddenSize; h++) {
      const row = h * this.inputSize;

      for (let j = 0; j < this.inputSize; j++) {
        this.W1[row + j] -= this.learningRate * dz1[h] * t[j];
      }

      this.b1[h] -= this.learningRate * dz1[h];
    }

    return loss / this.addressBits;
  }

  train(samples, { epochs = 1000, shuffle = true } = {}) {
    if (!Array.isArray(samples) || samples.length === 0) {
      throw new Error("samples must be a non-empty array.");
    }

    const order = samples.map((_, i) => i);
    let finalLoss = 0;

    for (let epoch = 0; epoch < epochs; epoch++) {
      if (shuffle) {
        for (let i = order.length - 1; i > 0; i--) {
          const j = Math.floor(this.rand() * (i + 1));
          [order[i], order[j]] = [order[j], order[i]];
        }
      }

      let totalLoss = 0;

      for (const idx of order) {
        const sample = samples[idx];
        totalLoss += this.trainOne(sample.t, sample.i);
      }

      finalLoss = totalLoss / samples.length;
    }

    return finalLoss;
  }
} // end class

/** Example Usage */

const axiomCount = 100_000;

const ann = new AxiomAddressANN({
  inputSize: 4,
  hiddenSize: 64,
  axiomCount,
  learningRate: 0.03,
  seed: 42
});

const samples = [
  { t: [1, 2, 0, 0], i: 0 },
  { t: [0, 0, 1, 0], i: 0 },
  { t: [1, 0, 2, 0], i: 1 },
  { t: [0, 0, 0, 1], i: 1 }
];

ann.train(samples, { epochs: 5000 });

// 1 + 1 + 1 + 1
const t = [3, 4, 0, 0];

// 1 + 1 + 1 + 1
//const t = [0, 0, 0, 1];

const result = ann.predictAddress( t );

console.log(result);