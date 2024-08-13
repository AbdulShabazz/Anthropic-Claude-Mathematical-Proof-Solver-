
try {

    /** Benchmark 1ms */

    let _input = document.getElementById ('input');
    let _output = document.getElementById ('output');
    let _lineNumbers = document.getElementById ('line-numbers');

    function solveProblem () {
        rewriteHistoryProofFoundFlag = false;
        const { axioms, proofStatement } = parseInput (_input.value);
        const startTime = performance.now ();
        _output.value = generateProof (axioms, proofStatement);
        output.value += `\n\nTotal runtime: ${performance.now () - startTime} Milliseconds`;
    } // end solveProblem

    function parseInput (input) {
        let lines = input.split ('\n').filter (line => line.trim () && !line.startsWith ('//'));
        let axioms = new Set ();

        lines.slice (0, -1).forEach ((line,k,thisArray) => {
            const parts = line.split (/[~<]?=+[>]?/g).map (s => s.trim ());
            parts.forEach ((part, i) => {
                parts.slice (i + 1).forEach ((otherPart, j, me) => {
                    axioms.add ({ subnets: `${part} = ${otherPart}`, axiomID: `axiom_${k+1}.0`});
                });
            });
        });

        const sortedAxioms = Array.from (axioms)
            .map (axiom => {
                axiom.subnets = axiom.subnets
                    .split (' = ')
                        .sort ((a, b) => a.length <= b.length)
                            .map ((pair,i,me) => pair.match (/\S+/g));
                return axiom;
            });

        const proofStatement = lines [lines.length - 1];

        return {
            axioms: sortedAxioms,
            proofStatement: proofStatement
        };
    } // end parseInput

    function generateProof (axioms, proofStatement) {
        let steps = [];
        let [lhs, rhs] = proofStatement
            .split (/[~<]?=+[>]?/g)
                .map (s => s.trim ().split (/\s+/));

        const proofFound = (() => {
            if (lhs.join (' ') == rhs.join (' '))
                return true;
            let ret = applyRules ([[...lhs], [...rhs]],'reduce');
            ret == (lhs.join (' ') == rhs.join (' '));
            !ret && (steps = []) && (ret = applyRules ([[...lhs], [...rhs]], 'expand'));
            return ret;
        })();
        
        return `${proofFound ? 'Proof' : 'Partial-proof'} found!\n\n${proofStatement}, (root)\n` +
        steps
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
            .join ('\n') +
                (proofFound ? '\n\nQ.E.D.' : '');

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
        } // end applyRules

    } // end generateProof

    function applyRule (expression, axioms, action) {
        const I = axioms.length;
        for (let i = 0; i < I; i++) {
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
    
    Object.prototype._tryReplace = function(from, to) {
        if (from.length > this.length) return false;
      
        let self = [...this];
        const I = from.length;
        let J = self.length;
        const J2 = to.length;
        let rewriteFoundFlag = false;
        let i = 0;
      
        for (let j = 0; j < J; j++) {
            if (from [i] == self [j]) {
                self [j] = '';
                if (++i == I) {
                    self.splice (j, 0, ...to);
                    J = self.length;
                    i = 0;
                    rewriteFoundFlag = true;
                }
            }
        }

        const rewriteSZArray = rewriteFoundFlag 
            ? self.filter (Boolean) 
            : false ;

        return rewriteSZArray;
    }

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
