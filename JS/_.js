
try {

    /** Benchmark: 2ms (test case 246) */
    
    const NUM_WORKERS = 4;
    const _workerScript = 
`
const self = this;
self.proofFoundEvent = false;
self.addEventListener ('proofFoundEvent', (e) => {    
    self.proofFoundEvent = true;
});
self.onmessage = function (e) {
    self.proofFoundEvent = false;
    const { data, strategy } = e.data;
    ({ rewriteStrategy, subnet, lhs, rhs, axioms, steps, proofStatement, startTime } = data);
    const result = applyRules (axioms, proofStatement.guidZ, [[...lhs], [...rhs]], strategy);
    self.postMessage({ proofFound: result, steps: steps?.length > 0 ? steps : [], proofStatement, rewriteStrategy, subnet, lhs, rhs, startTime });
    return;

    function applyRules (tmpAxioms, guidZ, sides, action) {
        sides = sides.map ((current,idx,me) => {
            let lastGUIDZ = guidZ;
            let changed;
            const side = idx == 0 ? 'lhs' : 'rhs' ;
            do {
                changed = applyRule (lastGUIDZ, current, tmpAxioms, action);
                if (changed) {
                    steps.push ({ side, action, result: [...changed.result], axiomID: changed.axiomID, other: [] });
                    current = changed.result;
                    lastGUIDZ = changed.axiomRewriteID;
                }
            } while (changed);
            return current;
        });
        return (sides [0].join (' ') == sides [1].join (' '));

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
                    return {
                        result: rewriteFound,
                        axiomID: axiom.axiomID,
                        axiomRewriteID: uuid,
                    };
                }
            } // end for (let i = 0; i < I; i++)
            return null;
        } // end applyRule

    } // end applyRules

} // end self.onmessage

function _scope_satisfied(tok, lhs, l, rhs, r) {
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
} // end _scope_satisfied

Array.prototype._tryReplace = function(from, to) {
    if (from.length > this.length) return false;

    let i = 0;
    const I = from.length;
    const J = this.length;
    const rewriteSZArray = [];
    let rewriteFoundFlag = false;
    const boundScopeSatisfied = (tok,j,i) => 
        _scope_satisfied(tok, this, j, from, i);

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
} // end Array.prototype._tryReplace
`;

    // Create an ArrayBuffer to store the counters
    const _sharedCounters = new Uint8Array(2);
    
    const REDUCE_INDEX = 0;
    const EXPAND_INDEX = 1;

    let _results = new Map ();
    const blob = new Blob([_workerScript], { type: 'application/javascript' });
    const workers = Array.from({ length: NUM_WORKERS }, (_,idx,me) => {
        let w = new Worker(URL.createObjectURL(blob));
        w.workerID = idx;
        w.onmessage = (e)=> {
            if (e.data?.proofFound != null) {
                let bestResult;
                const tmpData = e.data; 
                const tmpIndir = tmpData.rewriteStrategy;
                
                const tmpCompletedWorkersZ = ((i) => {
                    (tmpIndir == 'reduce') 
                        ? Atomics.add (_sharedCounters, REDUCE_INDEX, 1) 
                        : Atomics.add (_sharedCounters, EXPAND_INDEX, 1) ;
                    const retvalZ = (tmpIndir == 'reduce') 
                        ? Atomics.load (_sharedCounters, REDUCE_INDEX)
                        : Atomics.load (_sharedCounters, EXPAND_INDEX) ;
                    return retvalZ;
                })(0);
                const allWorkersCompleted = (Atomics.load (_sharedCounters, REDUCE_INDEX) == 2 && Atomics.load (_sharedCounters, EXPAND_INDEX) == 2);
                if(_results.get (tmpIndir) == null)
                    _results.set (tmpIndir, []);                    
                const tmpResults = _results.get (tmpIndir);
                tmpResults.push(tmpData);
                if (tmpCompletedWorkersZ == 2) {
                    if (allWorkersCompleted){
                        const maxReduceExpandRewrites = ((x) => {
                            const maxReduceRewritesZ = _results.get ('reduce')[0].steps.length 
                                + _results.get ('reduce')[1].steps.length ;
                            const maxExpandRewritesZ = _results.get ('expand')[0].steps.length 
                                + _results.get ('expand')[1].steps.length ;
                            return { maxReduceRewritesZ, maxExpandRewritesZ };
                        })(0);
                        const indirectionSZ = maxReduceExpandRewrites.maxReduceRewritesZ 
                            > maxReduceExpandRewrites.maxExpandRewritesZ
                            ? 'reduce'
                            : 'expand' ;                            
                        let localProofstepObj = structuredClone(_results.get (indirectionSZ)[0]);
                        _results
                            .get (indirectionSZ)[1]
                                .steps
                                    .forEach((tt,k,thisArray) => {
                            localProofstepObj.steps.push(tt);

                        });
                        // Attach the other subnet to the partial-proof
                        if (localProofstepObj.subnet == 'lhs'){
                            localProofstepObj.rhs = _results.get (indirectionSZ)[1].rhs;
                        } else {                                
                            localProofstepObj.lhs = _results.get (indirectionSZ)[1].lhs;
                        }
                        bestResult = localProofstepObj;                        
                    } // end if (allWorkersCompleted)
                    const tmpLHS = tmpResults[0].subnet == 'lhs' 
                        ? tmpResults[0] 
                        : tmpResults[1] ;
                    const tmpRHS = tmpResults[0].subnet == 'lhs' 
                        ? tmpResults[1] 
                        : tmpResults[0] ;
                    const tmpLHSString = returnLastProofStepZ(tmpLHS.steps, tmpLHS.lhs);
                    const tmpRHSString = returnLastProofStepZ(tmpRHS.steps, tmpRHS.rhs);
                    const resolveFirstFlag = (tmpLHSString == tmpRHSString) ;
                    if (resolveFirstFlag) {
                        w.dispatchEvent(new CustomEvent('proofFoundEvent', { workerID: w.workerID }));
                        tmpRHS.steps.forEach((u,jdx,metoo) => {
                            tmpLHS.steps.push(u);
                        });
                        tmpLHS.proofFound = true;
                        tmpLHS.rhs = tmpRHS.rhs;
                        bestResult = tmpLHS;
                    }

                    function returnLastProofStepZ (tmpSteps,tmpSZArray) {
                        if(tmpSteps?.length > 0)
                            return tmpSteps._last().result.join (' ');
                        return tmpSZArray.join (' ');
                    }
                }
                if (bestResult) {
                    ({ lhs, rhs, proofStatement, startTime } = bestResult);
                    const proofStackString = `${bestResult.proofFound ? 'Proof' : 'Partial-proof'} found!\n\n${proofStatement.subnets[0].join(' ')} = ${proofStatement.subnets[1].join(' ')}, (root)\n` +
                        bestResult.steps
                            .map((step, i, thisArray) => {
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
                                return `${currentSide.join(' ')} = ${otherSide.join(' ')}, (${side} ${action}) via ${axiomID}`;
                            })
                            .join('\n') +
                                (bestResult.proofFound ? '\n\nQ.E.D.' : '');

                    _output.value = proofStackString + `\n\nTotal runtime: ${performance.now () - startTime} Milliseconds`;
                } // end if (bestResult)
                
            } // end if (e.data?.proofFound != null) 
        }; // end onmessage
        return w;
    });
    
    let _input = document.getElementById ('input');
    let _output = document.getElementById ('output');
    let _lineNumbers = document.getElementById ('line-numbers');

    Array.prototype._last = function() {
        const key = this.length - 1;
        const val = this[key];
        return val;
    }

    function solveProblem () {
        const {axioms, proofStatement} = parseInput (_input.value);
        generateProof (axioms, proofStatement, _output);
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
            const subnetReduceFlag = Boolean(/^lhs/.test(indirectionSZ)); // reduce operation: lhs => rhs
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

    function generateProof (axioms, proofStatement, _) {
        let steps = [];
        let [lhs, rhs] = proofStatement.subnets;

        _sharedCounters[0] = _sharedCounters[1] = 0;
        _results = new Map ();
        const startTime = performance.now ();

        const workerData = [
            {
                rewriteStrategy: 'reduce',
                subnet: 'lhs',
                lhs: lhs,
                rhs: [],
                steps: [],
                axioms: axioms,
                proofStatement: proofStatement,
                startTime: startTime,
            },
            {
                rewriteStrategy: 'reduce',
                subnet: 'rhs',
                lhs: [],
                rhs: rhs,
                steps: [],
                axioms: axioms,
                proofStatement: proofStatement,
                startTime: startTime,
            },
            {
                rewriteStrategy: 'expand',
                subnet: 'lhs',
                lhs: lhs,
                rhs: [],
                steps: [],
                axioms: axioms,
                proofStatement: proofStatement,
                startTime: startTime,
            },
            {
                rewriteStrategy: 'expand',
                subnet: 'rhs',
                lhs: [],
                rhs: rhs,
                steps: [],
                axioms: axioms,
                proofStatement: proofStatement,
                startTime: startTime,
            },
        ]; // end workerData[]

        workers.forEach((w,idx,me) => {
            const tmpwWorkerData = workerData[idx];
            w.postMessage ({
                data: tmpwWorkerData,
                strategy: tmpwWorkerData.rewriteStrategy,
            });
        }); // end workers.forEach

        //_output.value = "Working...";
    } // end generateProof

    function _scope_satisfied(tok, lhs, l, rhs, r) {
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
    } // end _scope_satisfied

    Array.prototype._tryReplace = function(from, to) {
        if (from.length > this.length) return false;
    
        let i = 0;
        const I = from.length;
        const J = this.length;
        const rewriteSZArray = [];
        let rewriteFoundFlag = false;
        const boundScopeSatisfied = (tok,j,i) => 
            _scope_satisfied(tok, this, j, from, i);
    
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

    function updateLineNumbers () {
        const lines = _input.value.split ('\n');
        let i = 1;
        _lineNumbers.innerHTML = lines
            .map ((u, index) => /^[^\/\t\s\n]+/.test(u) ? i++ : '')
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
