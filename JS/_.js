
try {

    /** Benchmark <14ms (test case 246) */

    const NUM_WORKERS = 2;
    const workerScript =
`
const self = this;
self.proofFoundEvent = false;
self.addEventListener ('proofFoundEvent', (e) => {    
    self.proofFoundEvent = true;
    //if (e.workerID != self.workerID)
        //self.terminate ();
});
self.onmessage = function (e) {
    self.proofFoundEvent = false;
    const { data, strategy } = e.data;
    const { lhs, rhs, axioms, steps, proofStatement, startTime } = data;
    const result = applyRules ([[...lhs], [...rhs]], strategy, axioms);
    self.postMessage({ proofFound: result, steps: steps?.length > 0 ? steps : [], proofStatement, lhs, rhs, startTime });
    result && self.dispatchEvent(new CustomEvent('proofFoundEvent', { workerID: self.workerID }));
    //self.terminate();
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
    
Object.prototype._scope_satisfied = function(etok,lhs,li,rhs,ri){
    var i = 1;
    var end_scope = { "(":")", "{":"}" };
    var sat = true;
    if (lhs[li] != rhs[ri]) {
        sat = false;
    } else if (etok in end_scope) {
        if (((li+i) in lhs) && ((ri+i) in rhs)) {
            var ltok = lhs [li+i];
            var rtok = rhs [ri+i];
            var I = rhs.length; // Math.min(lhs.length,rhs.length) //
            etok = end_scope [etok];
            while (i++<I){
                if (ltok!=rtok){
                    sat = false;
                    break;
                }
                if(rtok == etok){
                    break;
                }
                ltok = lhs[li+i];
                rtok = rhs[ri+i];
            }
        } else {
            sat = false;
        }
    } // test(etok) //
    return sat;
} // end Object.prototype._scope_satisfied

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
        if (self._scope_satisfied(tok,self,j,from,i) 
                && from [i] === tok){
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

    let results = [];
    const _completedWorkersZ = new Uint32Array(1);
    const blob = new Blob([workerScript], { type: 'application/javascript' });
    const workers = Array.from({ length: NUM_WORKERS }, (_,idx,me) => {
        let w = new Worker(URL.createObjectURL(blob));
        w.workerID = idx;
        w.onmessage = (e)=> {
            let bestResult;
            if (e.data?.proofFound != null) {
                Atomics.add (_completedWorkersZ,0,1);
                results.push(e.data);
                if (e.data.proofFound == true) {
                    bestResult = e.data;
                } else if (Atomics.load(_completedWorkersZ,0) == 2) {
                    const resolveFirstFlag 
                        = (results[0].steps?.length 
                            >= results[1].steps?.length) ;
                    bestResult = (resolveFirstFlag) ? results[0] : results[1];
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
    let lineNumbers = document.getElementById ('line-numbers');

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
                .map (s => s.trim ().split (/\s+/));

        //const startTime = performance.now ();
    
        /* let */ results = [];
        /* let */ _completedWorkersZ[0] = 0;

        const strategy = ['reduce', 'expand'];

        const workerData = {
            lhs: [...lhs],
            rhs: [...rhs],
            steps: [],
            axioms: axioms,
            proofStatement: proofStatement,
            startTime: performance.now (),
        };

        workers.forEach((w,idx,me) => {
            w.postMessage ({
                data: structuredClone (workerData), 
                strategy: strategy[idx],
            });
        }); // end workers.forEach

        _output.value = "Working...";
    } // end generateProof

    function updateLineNumbers () {
        const lines = _input.value.split ('\n');
        let i = 1;
        lineNumbers.innerHTML = lines
            .map ((u, index) => /^[^\/\t\s\n]+/.test(u) ? i++ : '')
                .join ('<br>');
    } // end updateLineNumbers

    _input.addEventListener ('keyup', function () {
        updateLineNumbers ();
    });

    _input.addEventListener ('scroll', function () {
        lineNumbers.scrollTop = this.scrollTop;
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
