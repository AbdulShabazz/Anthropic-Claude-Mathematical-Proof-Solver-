
try {

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
    const result = applyRules ([[...lhs], [...rhs]], strategy, axioms);
    self.postMessage({ proofFound: result, steps: steps?.length > 0 ? steps : [], proofStatement, rewriteStrategy, subnet, lhs, rhs, startTime });
    //result && self.dispatchEvent(new CustomEvent('proofFoundEvent', { workerID: self.workerID }));
    return;

    function applyRules (sides, action) {
        sides = sides.map ((current,idx,me) => {
            let changed;
            const side = idx == 0 ? 'lhs' : 'rhs' ;
            do {
                changed = applyRule (current, axioms, action);
                if (changed) {
                    steps.push ({ side, action, result: [...changed.result], axiomID: changed.axiomID, other: [] });
                    current = changed.result;
                }
            } while (changed);
            return current;
        });
        return (sides [0].join (' ') == sides [1].join (' '));            

        function applyRule (expression, axioms, action) {
            const I = axioms.length;
            for (let i = 0; i < I && self.proofFoundEvent == false; i++) {
                const axiom = axioms [i];
                const [left, right] = axiom.subnets;
                const match = action === 'reduce' ? left : right;
                const replacer = action === 'reduce' ? right : left;
                const rewriteFound = expression._tryReplace (match, replacer);
                if (rewriteFound) {
                    return {
                        result: rewriteFound,
                        axiomID: axiom.axiomID,
                    };
                }
            }
            return null;
        } // end applyRule
    } // end applyRules
}

Object.prototype._tryReplace = function (from, to) {
    let ret = false;
    if (from.length > this.length)
        return false;
    let i = 0;
    let j = 0;
    let self = [...this];
    let tokenIDX = [];
    let rewriteFoundFlag;
    for (let tok of self) {
        if (tok == from [i]){
            tokenIDX.push (j);
            ++i;
        }
        !ret && (ret = (from.length == i));
        if (ret){
            tokenIDX.forEach ((k,idx,me) => {
                self [k] = '';
            });
            self [j] = to.join (' ');
            i = 0;
            ret = false;
            tokenIDX = [];
            !rewriteFoundFlag && (rewriteFoundFlag = true);
        }
        ++j;
    }
    if (!rewriteFoundFlag)
        return false;
    const rewriteString = self
        .join(' ')
            .match(/\\S+/g) 
                || [];
    return rewriteString;
} // end Object.prototype._tryReplace
`;

    // Create an ArrayBuffer to store the counters
    const _sharedCounters = new Uint8Array(2);

    // Index 0 for _allReduceCompletedWorkersZ, index 1 for _allExpandCompletedWorkersZ
    const REDUCE_INDEX = 0;
    const EXPAND_INDEX = 1;

    let _results = new Map ();
    /* let _allReduceCompletedWorkersZ = 0; */
    /* let _allExpandCompletedWorkersZ = 0; */
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
                    const retvalZ = (tmpIndir == 'reduce') 
                        ? Atomics.add (_sharedCounters, REDUCE_INDEX, 1) + 1/* ++_allReduceCompletedWorkersZ */ 
                        : Atomics.add (_sharedCounters, EXPAND_INDEX, 1) + 1/* ++_allExpandCompletedWorkersZ */ ;
                    return retvalZ;
                })(0);
                const allWorkersCompleted = (Atomics.load (_sharedCounters, REDUCE_INDEX)/* _allReduceCompletedWorkersZ */ == 2 && Atomics.load (_sharedCounters, EXPAND_INDEX)/* _allExpandCompletedWorkersZ */ == 2);
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
                    const proofStackString = `${bestResult.proofFound ? 'Proof' : 'Partial-proof'} found!\n\n${proofStatement}, (root)\n` +
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

    function parseInput(input) {
        let lines = input
            .split('\n')
                .filter(line => line.trim() && !line.startsWith('//'));
        let axioms = new Set ();

        lines
            .slice(0, -1)
                .forEach((line,k,thisArray) => {
                    const parts = line.split(/[~<]?=+[>]?/g).map(s => s.trim());
                    parts.forEach((part, i) => {
                        parts.slice(i + 1).forEach((otherPart, j, me) => {
                            axioms.add({ subnets: `${part} = ${otherPart}`, axiomID: `axiom_${k+1}.0`});
                        });
                    });
                });

        const sortedAxioms = Array
            .from(axioms)
                .map(axiom => {
                    axiom.subnets = axiom.subnets
                        .split(' = ')
                            .sort((a, b) => a.length <= b.length)
                                .map((pair,i,me) => pair.split(/\s+/));
                    return axiom;
                });

        const proofStatement = lines[lines.length - 1];

        return {
            axioms: sortedAxioms,
            proofStatement: proofStatement
        };
    } // end parseInput

    function generateProof (axioms, proofStatement, _) {
        let steps = [];
        let [lhs, rhs] = proofStatement
            .split (/[~<]?=+[>]?/g)
                .map ((u,idx,me) => {
                    const ret = u.match (/\S+/g);
                    return ret;
                });

        /* let */ _sharedCounters[0] = _sharedCounters[1] = 0;
        /* let */ _results = new Map ();
        /* let _allReduceCompletedWorkersZ = 0; */
        /* let _allExpandCompletedWorkersZ = 0; */
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
        ];

        workers.forEach((w,idx,me) => {
            const tmpwWorkerData = workerData[idx];
            w.postMessage ({
                data: tmpwWorkerData,
                strategy: tmpwWorkerData.rewriteStrategy,
            });
        }); // end workers.forEach
    } // end generateProof

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
