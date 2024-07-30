
try {

    let _input = document.getElementById ('input');
    let _output = document.getElementById ('output');
    let lineNumbers = document.getElementById ('line-numbers');

    function solveProblem () {
        rewriteHistoryProofFoundFlag = false;
        const {axioms, proofStatement} = parseInput (_input.value);
        const startTime = performance.now ();
        _output.value = generateProof (axioms, proofStatement);
        output.value += `\n\nTotal runtime: ${performance.now () - startTime} Milliseconds`;
    } // end solveProblem

    function parseInput(input) {
        let lines = input.split('\n').filter(line => line.trim() && !line.startsWith('//'));
        let axioms = new Set ();

        lines.slice(0, -1).forEach(line => {
            const parts = line.split(/[~<]?=+[>]?/g).map(s => s.trim());
            parts.forEach((part, i) => {
                parts.slice(i + 1).forEach((otherPart, j, me) => {
                    axioms.add({ subnets: `${part} = ${otherPart}`, axiomID: `axiom_${i+1}.0`});
                });
            });
        });

        const sortedAxioms = Array.from(axioms)
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
            steps.map (step => `${step.side === 'lhs' ? step.result.join (' ') : step.other.join (' ')} = ${step.side === 'lhs' ? step.other.join (' ') : step.result.join (' ')}, (${step.side} ${step.action}) via ${step.axiomID}`).join ('\n') +
            (proofFound ? '\n\nQ.E.D.' : '');

        function applyRules (sides, action) {
            sides = sides.map ((current,idx,me) => {
                let changed;
                const other = idx == 0 ? me [1] : me [0] ;
                const side = idx == 0 ? 'lhs' : 'rhs' ;
                do {
                    changed = applyRule (current, axioms, action);
                    if (changed) {
                        steps.push ({ side, action, result: [...changed.result], axiomID: changed.axiomID, other: [...other] });
                        current = changed.result;
                    }
                } while (changed && current.join (' ') !== other.join (' '));
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
            if (from [i] === tok){
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
        self = self
            .join (' ')
                .split (/\s+/)
                    .filter (u => u)
                        .map ((s,index,me) => s
                            .trim ());
        return self;
    } // end Object.prototype._tryReplace

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