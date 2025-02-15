
try {

    /** Benchmark 1ms (test case 246) */

    let _input = document.getElementById ('input');
    let _output = document.getElementById ('output');
    let _lineNumbers = document.getElementById ('line-numbers');

    let LHS_commit_history = new Set();
    let RHS_commit_history = new Set();

    function solveProblem () {
        rewriteHistoryProofFoundFlag = false;
        const { axioms, proofStatement } = parseInput (_input.value);
        const startTime = performance.now ();
        _output.value = generateProof (axioms, proofStatement);
        _output.value += `\n\nTotal runtime: ${performance.now () - startTime} Milliseconds`;
    } // end solveProblem

    function parseInput (input) {
        let lines = input
            .split ('\n')
                .filter (line => line.trim () && !line.startsWith ('//'));
        let axiomsSet = new Set ();

        lines
            .slice ()
                .forEach ((line,k,thisArray) => {
                    const parts = line
                        .split (/[~<]?=+[>]?/g)
                            .map (s => s.trim ());
                    parts.forEach ((part, i) => {
                        parts.slice (i + 1).forEach ((otherPart, j, me) => {
                            axiomsSet.add ({ subnets: `${part} = ${otherPart}`, axiomID: `axiom_${k+1}.0` , guidZ: k });
                        });
                    });
                });

        const sortedAxioms = Array.from (axiomsSet)
            .map (axiom => {
                axiom.subnets = axiom.subnets
                    .split (' = ')
                        .sort ((a, b) => a.length <= b.length)
                            .map ((pair,i,me) => {
                                return pair.match (/\S+/g);
                            });
                return axiom;
            });

        buildAllSubnetCallGraphsF (sortedAxioms);

        const proofStatement = sortedAxioms [sortedAxioms.length - 1];

        return {
            axioms: sortedAxioms,
            proofStatement: proofStatement
        };

        function buildAllSubnetCallGraphsF (unsortedAxiomsArray) {
            const I = unsortedAxiomsArray.length;
            const J = unsortedAxiomsArray.length - 1; // disallow root

            for (let i = 0; i < I; i++) {
                let axiom_00 = unsortedAxiomsArray [i];
                for (let j = 0; j < J; j++) {
                    if (i == j) continue ;
                    let axiom_01 = unsortedAxiomsArray [j];
                    let [ axiom_01_lhs, axiom_01_rhs ] = axiom_01.subnets;
                    buildSubnetCallGraphF (axiom_00, j, axiom_01_lhs, 'lhs');
                    buildSubnetCallGraphF (axiom_00, j, axiom_01_rhs, 'rhs');
                } // end for (let j = 0; j < J; j++)
            } // end for (let i = 0; i < I; i++)

        } // end buildSubnetCallGraphs (...)

        function buildSubnetCallGraphF (axiom, i, from, indirectionSZ) {
            let [ lhs, rhs ] = axiom.subnets;
            const ci_lhsZ = lhs._tryReplace (from, [true]);
            const ci_rhsZ = rhs._tryReplace (from, [true]);
            const subnetReduceFlag = Boolean(/^lhs/.test(indirectionSZ)); // reduce: lhs => rhs
            if (ci_lhsZ && subnetReduceFlag) {
                AddToLHSReduce (axiom, i);
            } else if (ci_lhsZ) {
                AddToLHSExpand (axiom, i);
            }
            if (ci_rhsZ && subnetReduceFlag) {
                AddToRHSReduce (axiom, i);
            } else if (ci_rhsZ) {
                AddToRHSExpand (axiom, i);
            }
        } // end buildSubnetCallGraphF (axiom, from, to)

        function AddToLHSReduce (axiom, i) {
            (axiom._lhsReduce == undefined) && (axiom._lhsReduce = []);
            axiom._lhsReduce.push (i);
        } // end AddToLHSReduce

        function AddToLHSExpand (axiom, i) {
            (axiom._lhsExpand == undefined) && (axiom._lhsExpand = []);
            axiom._lhsExpand.push (i);
        } // end AddToLHSExpand

        function AddToRHSReduce (axiom, i) {
            (axiom._rhsReduce == undefined) && (axiom._rhsReduce = []);
            axiom._rhsReduce.push (i);
        } // end AddToRHSReduce

        function AddToRHSExpand (axiom, i) {
            (axiom._rhsExpand == undefined) && (axiom._rhsExpand = []);
            axiom._rhsExpand.push (i);
        } // end AddToRHSExpand

    } // end parseInput

    function generateProof (axioms, proofStatement) {
        let steps = [];
        let proofsteps = []
        let [lhs, rhs] = proofStatement.subnets;
        const proofFound = (() => {
            if (lhs.join (' ') == rhs.join (' '))
                return true;
            let ret = applyAxioms (axioms, proofStatement.guidZ, [[...lhs], [...rhs]],'reduce');
            ret == (lhs.join (' ') == rhs.join (' '));
            // reduce failed? Try expand!
            !ret
                && (proofsteps.push ([...steps]))
                    && (steps = [])
                        && (ret = applyAxioms (axioms, proofStatement.guidZ, [[...lhs], [...rhs]], 'expand'));
            proofsteps.push ([...steps]);
            return ret;
        })();

        !proofFound 
            && (result = proofsteps
                .sort((a,b) => b.length > a.length)
                    .shift());

        return `${proofFound ? 'Proof' : 'Partial-proof'} found!\n\n${proofStatement.subnets [0].join (' ')} = ${proofStatement.subnets [1].join (' ')}, (root)\n`
            + steps
                .map ((step, i) => {
                    // update proofstep
                    const { side, result, action, axiomID } = step;
                    const isLHS = side === 'lhs';
                    const currentSide = isLHS ? result : lhs;
                    const otherSide = isLHS ? rhs : result;

                    // update global expression
                    if (isLHS) {
                        lhs = result;
                    } else {
                        rhs = result;
                    }

                    // return rewrite string
                    return `${currentSide.join (' ')} = ${otherSide.join (' ')}, (${side} ${action}) via ${axiomID}`;
                })
                .join ('\n')
                    + (proofFound ? '\n\nQ.E.D.' : '');

        function _applyAxioms (tmpAxioms, guidZ, sides, action) {
            sides = sides.map ((current,idx,me) => {
                let lastGUIDZ = guidZ;
                let changed;
                const side = idx == 0 ? 'lhs' : 'rhs' ;
                do {
                    changed = applyRule (lastGUIDZ, current, tmpAxioms, action);
                    for (let ch of changed) {
                        steps.push ({ side, action, result: [...ch.result], axiomID: ch.axiomID, other: [] });
                        current = ch.result;
                        lastGUIDZ = ch.axiomRewriteID;
                    }
                } while (changed?.length > 0);
                return current;
            });
            return (sides [0].join (' ') == sides [1].join (' '));
        } // end applyAxioms

        function applyAxioms (tmpAxioms, guidZ, sides, action) {
            /*
            sides = sides.map ((current,idx,me) => {
                let lastGUIDZ = guidZ;
                let changed;
                const side = idx == 0 ? 'lhs' : 'rhs' ;
                do {
                    changed = applyRule (lastGUIDZ, current, tmpAxioms, action);
                    for (let ch of changed) {
                        steps.push ({ side, action, result: [...ch.result], axiomID: ch.axiomID, other: [] });
                        current = ch.result;
                        lastGUIDZ = ch.axiomRewriteID;
                    }
                } while (changed?.length > 0);
                return current;
            });
            return (sides [0].join (' ') == sides [1].join (' '));
            */
        } // end applyAxioms

    } // end generateProof

    function applyRule (guidZ, expression, tmpAxioms, action) {
        const axiomIDS = (() => {
            let tmpA = [];
            switch (action) {
                case 'reduce':
                    if (tmpAxioms [guidZ]?._lhsReduce) {
                        tmpA.push (
                            ...tmpAxioms [guidZ]?._lhsReduce
                        );
                    } 
                    if (tmpAxioms [guidZ]?._rhsReduce) {
                        tmpA.push (
                            ...tmpAxioms [guidZ]?._rhsReduce
                        );
                    }
                    break;
                case 'expand':
                    if (tmpAxioms [guidZ]?._lhsExpand) {
                        tmpA.push (
                            ...tmpAxioms [guidZ]?._lhsExpand
                        );
                    } 
                    if (tmpAxioms [guidZ]?._rhsExpand) {
                        tmpA.push (
                            ...tmpAxioms [guidZ]?._rhsExpand
                        );
                    }
                    break;
            } // end switch (action)
            return tmpA;
        }) ();
        let batchRewrites = [];
        const I = axiomIDS.length;
        for (let i = 0; i < I; i++) {
            const uuid = axiomIDS [i];
            if (uuid == guidZ)
                continue;
            const axiom = tmpAxioms [uuid];
            const [left, right] = axiom.subnets;
            const from = action === 'reduce' ? left : right;
            const to = action === 'reduce' ? right : left;
            const rewriteFound = expression._tryReplace (from, to);
            if (rewriteFound) {
                batchRewrites.push( {
                    result: rewriteFound,
                    axiomID: axiom.axiomID,
                    axiomRewriteID: uuid,
                });
            }
        } // end for (let i = 0; i < I; i++)
        return batchRewrites;
    } // end applyRule

    Object.prototype._tryReplace = function(from, to) {
        if (from.length > this.length) return false;

        let i = 0;
        const I = from.length;
        const J = this.length;
        const rewriteSZArray = [];
        let rewriteFoundFlag = false;
        const boundScopeSatisfied = (tok,j,i) => 
            this._scope_satisfied(tok, this, j, from, i);

        let resp;
        for (let j = 0; j < J; j++) {
            const tok = this [j];
            if (resp = boundScopeSatisfied (tok, j, i)) {
                i += resp.j - j;
                j = resp.j;
                if (++i === I) {
                    i = 0;
                    rewriteSZArray.push (...to);
                    rewriteFoundFlag = true;
                    continue;
                }
            } else {
                rewriteSZArray.push (tok);
            }
        }

        return rewriteFoundFlag
            ? rewriteSZArray
            : false;
    } // end Object.prototype._tryReplace

    Object.prototype._scope_satisfied = function(tok, lhs, l, rhs, r) {
        if (lhs[l] !== rhs[r]) return false;

        const endScope = { "(": ")", "{": "}" };
        if (!(tok in endScope)) return { j : l };
        const endToken = endScope[tok];
        const I = rhs.length;
        const J = lhs.length;

        for (let i = 1; (r + i < I) && (l + i < J); i++) {
            const ltok = lhs[l + i];
            const rtok = rhs[r + i];
            
            if (rtok === endToken) return { j : l + i };
            if (ltok !== rtok) return false;
        }

        return false;
    } // end Object.prototype._scope_satisfied

    /**************************************************
     * Term-Rewriting System with Generator Function
     **************************************************/
    function* rewriteGenerator(theorem, theorem_to_prove, axioms) {
        // Track strings that we have seen already
        const visited = new Set();
        // Initialize our queue with the starting theorem
        const queue = [theorem];
        
        // Mark the starting theorem as visited
        visited.add(theorem);

        while (queue.length > 0) {
            // Take the next item from the queue
            const current = queue.shift();
            
            // Yield the current rewrite step
            yield current;

            // Check if we have reached our desired theorem
            if (current == theorem_to_prove) {
                // Stop the generator once the target is found
                return;
            }

            // Attempt all possible rewrites by applying every axiom
            for (const axiom of axioms) {
                for (const from in axiom) {
                    const to = axiom[from];

                    // Identify the placeholder pattern in the theorem text, e.g. {a} -> {b}
                    const matchPattern = `{${from}}`;
                    const rewritePattern = `{${to}}`;

                    // For each place that "from" occurs, replace and produce a new candidate
                    let startIndex = 0;
                    while (true) {
                        const idx = current.indexOf(matchPattern, startIndex);
                        if (idx === -1) {
                            break;
                        }
                        // Construct the new theorem string after rewriting
                        const newTheorem =
                            current.slice(0, idx) 
                                + rewritePattern 
                                    + current.slice(idx + matchPattern.length);

                        // If we have not seen this new rewrite, enqueue it for further exploration
                        if (!visited.has(newTheorem)) {
                            visited.add(newTheorem);
                            queue.push(newTheorem);
                        }

                        // Move past this occurrence to look for another
                        startIndex = idx + matchPattern.length;
                    }
                }
            }
        }
    } // rewriteGenerator(theorem, theorem_to_prove, axioms)

    /*
    
    // Example usage:    

    // Define your axioms: each object means '{key}' -> '{value}'
    const axioms = [
        { 'a': 'b' },
        { '0': '1' },
        { 'y': 'z' }
    ];

    // Starting theorem
    const theorem = '{a} + {0} + {y}';
    // Target theorem we wish to prove
    const theorem_to_prove = '{b} + {1} + {z}';

    // Instantiate the generator
    const generator = rewriteGenerator(theorem, theorem_to_prove, axioms);

    // Collect the steps in an array for inspection
    const proofSteps = [];
    for (const step of generator) {
        console.log('Rewrite step:', step);
        proofSteps.push(step);

        if (step === theorem_to_prove) {
            break;
        }
    }

    console.log(proofSteps,'\n\n');

    if(proofSteps[proofSteps.length-1] == theorem_to_prove) {    
        console.log('Q.E.D.');
    } else if (proofSteps.length > 0) {
        console.log('Partial-proof found.');
    } else {     
        // If we never encountered the theorem_to_prove, no successful proof was found
        console.log('No proof found.');
    }

    */

    function updateLineNumbers () {
        const lines = _input.value.split ('\n');
        let i = 1;
        _lineNumbers.innerHTML = lines
            .map ((u, index) => /^[^\/\t\s\n]+/.test (u) ? i++ : '')
                .join ('<br>');
    } // end updateLineNumbers

    _input.addEventListener ('keyup', function () {
        updateLineNumbers ();
    });

    _input.addEventListener ('scroll', function () {
        _lineNumbers.scrollTop = this.scrollTop;
    });

    updateLineNumbers ();

} catch (e) {
    output.value = JSON.stringify (e, ' ', 2);
}

input.value = input.value
? input.value :
`// Axioms and Lemmas
1 + 1 = 2
2 + 2 = 4

// Prove
1 + 2 + 1 = 4`;

output.value = '';
