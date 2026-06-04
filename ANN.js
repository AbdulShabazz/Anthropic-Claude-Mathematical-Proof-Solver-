"use strict";



/**
 * @description: ANN accepts LHS/RHS theorem features. 
 * Deterministic pseudo-random generator.
 * Keeps initialization reproducible.
 * 
 * @returns: Suitable rewrite Axiom (0-based index).
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
  return Math.max(0, x);
}

function reluDerivative(x) {
  return x > 0 ? 1 : 0;
}

function softmax(logits) {
  const max = Math.max(...logits);
  const exps = logits.map(x => Math.exp(x - max));
  const sum = exps.reduce((a, b) => a + b, 0);
  return exps.map(x => x / sum);
}

function argmax(arr) {
  let bestIndex = 0;
  let bestValue = arr[0];

  for (let i = 1; i < arr.length; i++) {
    if (arr[i] > bestValue) {
      bestValue = arr[i];
      bestIndex = i;
    }
  }

  return bestIndex;
}

class AxiomIndexANN {
  constructor({
    inputSize,
    hiddenSize,
    outputSize,
    learningRate = 0.03,
    seed = 1234
  }) {
    if (!Number.isInteger(inputSize) || inputSize <= 0) {
      throw new Error("inputSize must be a positive integer.");
    }

    if (!Number.isInteger(hiddenSize) || hiddenSize <= 0) {
      throw new Error("hiddenSize must be a positive integer.");
    }

    if (!Number.isInteger(outputSize) || outputSize <= 1) {
      throw new Error("outputSize must be an integer greater than 1.");
    }

    this.inputSize = inputSize;
    this.hiddenSize = hiddenSize;
    this.outputSize = outputSize;
    this.learningRate = learningRate;

    const rand = mulberry32(seed);

    // He-style small initialization for ReLU hidden layer.
    this.W1 = Array.from({ length: hiddenSize }, () =>
      Array.from({ length: inputSize }, () =>
        (rand() * 2 - 1) * Math.sqrt(2 / inputSize)
      )
    );

    this.b1 = Array.from({ length: hiddenSize }, () => 0);

    this.W2 = Array.from({ length: outputSize }, () =>
      Array.from({ length: hiddenSize }, () =>
        (rand() * 2 - 1) * Math.sqrt(2 / hiddenSize)
      )
    );

    this.b2 = Array.from({ length: outputSize }, () => 0);
  }

  validateInput(t) {
    if (!Array.isArray(t)) {
      throw new Error("Input t must be an array.");
    }

    if (t.length !== this.inputSize) {
      throw new Error(`Input t must have length ${this.inputSize}.`);
    }

    for (const x of t) {
      if (!Number.isFinite(x)) {
        throw new Error("Input t must contain only finite numbers.");
      }
    }
  }

  forward(t) {
    this.validateInput(t);

    const z1 = new Array(this.hiddenSize);
    const a1 = new Array(this.hiddenSize);

    for (let h = 0; h < this.hiddenSize; h++) {
      let sum = this.b1[h];

      for (let j = 0; j < this.inputSize; j++) {
        sum += this.W1[h][j] * t[j];
      }

      z1[h] = sum;
      a1[h] = relu(sum);
    }

    const z2 = new Array(this.outputSize);

    for (let k = 0; k < this.outputSize; k++) {
      let sum = this.b2[k];

      for (let h = 0; h < this.hiddenSize; h++) {
        sum += this.W2[k][h] * a1[h];
      }

      z2[k] = sum;
    }

    const probabilities = softmax(z2);

    return { z1, a1, z2, probabilities };
  }

  predict(t) {
    const { probabilities } = this.forward(t);
    return argmax(probabilities);
  }

  predictWithConfidence(t) {
    const { probabilities } = this.forward(t);
    const i = argmax(probabilities);

    return {
      i,
      confidence: probabilities[i],
      probabilities
    };
  }

  trainOne(t, expectedIndex) {
    this.validateInput(t);

    if (
      !Number.isInteger(expectedIndex) ||
      expectedIndex < 0 ||
      expectedIndex >= this.outputSize
    ) {
      throw new Error(`expectedIndex must be in [0, ${this.outputSize - 1}].`);
    }

    const { z1, a1, probabilities } = this.forward(t);

    // Cross-entropy gradient with softmax:
    // dL/dz2 = probabilities - oneHot(expectedIndex)
    const dz2 = probabilities.slice();
    dz2[expectedIndex] -= 1;

    const oldW2 = this.W2.map(row => row.slice());

    // Update W2 and b2.
    for (let k = 0; k < this.outputSize; k++) {
      for (let h = 0; h < this.hiddenSize; h++) {
        this.W2[k][h] -= this.learningRate * dz2[k] * a1[h];
      }

      this.b2[k] -= this.learningRate * dz2[k];
    }

    // Backpropagate into hidden layer.
    const dz1 = new Array(this.hiddenSize).fill(0);

    for (let h = 0; h < this.hiddenSize; h++) {
      let grad = 0;

      for (let k = 0; k < this.outputSize; k++) {
        grad += oldW2[k][h] * dz2[k];
      }

      dz1[h] = grad * reluDerivative(z1[h]);
    }

    // Update W1 and b1.
    for (let h = 0; h < this.hiddenSize; h++) {
      for (let j = 0; j < this.inputSize; j++) {
        this.W1[h][j] -= this.learningRate * dz1[h] * t[j];
      }

      this.b1[h] -= this.learningRate * dz1[h];
    }

    const loss = -Math.log(Math.max(probabilities[expectedIndex], 1e-12));
    return loss;
  }

  train(samples, { epochs = 1000, shuffle = true } = {}) {
    if (!Array.isArray(samples) || samples.length === 0) {
      throw new Error("samples must be a non-empty array.");
    }

    let lastLoss = 0;

    for (let epoch = 0; epoch < epochs; epoch++) {
      let totalLoss = 0;

      const order = samples.map((_, i) => i);

      if (shuffle) {
        // Deterministic-enough local shuffle using Math.random.
        // Replace with seeded shuffle if strict reproducibility is required.
        for (let i = order.length - 1; i > 0; i--) {
          const j = Math.floor(Math.random() * (i + 1));
          [order[i], order[j]] = [order[j], order[i]];
        }
      }

      for (const idx of order) {
        const sample = samples[idx];
        totalLoss += this.trainOne(sample.t, sample.i);
      }

      lastLoss = totalLoss / samples.length;
    }

    return lastLoss;
  }

  toJSON() {
    return {
      inputSize: this.inputSize,
      hiddenSize: this.hiddenSize,
      outputSize: this.outputSize,
      learningRate: this.learningRate,
      W1: this.W1,
      b1: this.b1,
      W2: this.W2,
      b2: this.b2
    };
  }

  static fromJSON(data) {
    const model = new AxiomIndexANN({
      inputSize: data.inputSize,
      hiddenSize: data.hiddenSize,
      outputSize: data.outputSize,
      learningRate: data.learningRate
    });

    model.W1 = data.W1;
    model.b1 = data.b1;
    model.W2 = data.W2;
    model.b2 = data.b2;

    return model;
  }
} // end class 

/** Example Usage */

const axioms = [
  "1 + 1 = 2",
  "2 + 2 = 4"
];

// Example training set.
// Each `t` is a symbol-tally vector t[+ 1 2 4 ...].
// Each `i` is the correct axiom index .
const samples = [
  { t: [1, 2, 0, 0], i: 0 },
  { t: [0, 0, 1, 0], i: 0 },
  { t: [1, 0, 2, 0], i: 1 },
  { t: [0, 0, 0, 1], i: 1 }
];

const ann = new AxiomIndexANN({
  inputSize: 4,
  hiddenSize: 8,
  outputSize: axioms.length,
  learningRate: 0.02,
  seed: 42
});

ann.train(samples, { epochs: 3000 });

// 1 + 1 + 1 + 1
//const t = [3, 4, 0, 0];

// 1 + 1 + 1 + 1
const t = [0, 0, 0, 1];

const result = ann.predictWithConfidence(t);

console.log("Input tally:", t);
console.log("Predicted axiom index:", result.i);
console.log("Predicted axiom:", axioms[result.i]);
console.log("Confidence:", result.confidence);
console.log("All probabilities:", result.probabilities);