
try {

    let _input = document.getElementById ('input');
    let _output = document.getElementById ('output');
    let lineNumbers = document.getElementById ('line-numbers');

    function solveProblem () {
        const {axioms, proofStatement} = parseInput (document.getElementById ('input').value);
        const startTime = performance.now ();
        document.getElementById ('output').value = generateProof (axioms, proofStatement);
        output.value += `\n\nTotal runtime: ${performance.now () - startTime} Milliseconds`;
    } // end solveProblem

    function parseInput (input) {
        const lines = input.split ('\n').filter (line => line.trim () && !line.startsWith ('//'));
        return {
            axioms: lines
                .slice (0, -1)
                    .map ((line,idx,me) => line
                        .split (/[~<]?=+[>]?/g)
                            .sort ((a,b) => a.length <= b.length )
                                .map ((s,idx,me) => s
                                    .trim ()
                                        .split (/\s+/))),
            proofStatement: lines [lines.length - 1]
        };
    } // end parseInput

    function generateProof (axioms, proofStatement) {
        let [lhs, rhs] = proofStatement.split (/[~<]?=+[>]?/g).map (s => s.trim ().split (/\s+/));
        let steps = [];

        const applyRules = (sides, action) => {
            sides = sides.map ((current,idx,me) => {
                let changed;
                const other = idx == 0 ? me [1] : me [0] ;
                const side = idx == 0 ? 'lhs' : 'rhs' ;
                do {
                    changed = applyRule (current, axioms, action);
                    if (changed) {
                        steps.push ({ side, action, result: [...changed.result], axiom: changed.axiom, other: [...other] });
                        current = changed.result;
                    }
                } while (changed && current.join (' ') !== other.join (' '));
                return current;
            });
            return (sides [0].join (' ') == sides [1].join (' '));
        };

        const proofFound = (() => {
            let ret = applyRules ([[...lhs], [...rhs]],'reduce');
            ret == (lhs.join (' ') == rhs.join (' '));
            !ret && (steps = []) && (ret = applyRules ([[...lhs], [...rhs]], 'expand'));
            return ret;
        })();

        return `${proofFound ? 'Proof' : 'Partial-proof'} found!\n\n${proofStatement}, (root)\n` +
            steps.map (step => `${step.side === 'lhs' ? step.result.join (' ') : step.other.join (' ')} = ${step.side === 'lhs' ? step.other.join (' ') : step.result.join (' ')}, (${step.side} ${step.action}) via ${step.axiom}`).join ('\n') +
            (proofFound ? '\n\nQ.E.D.' : '');
    } // end generateProof

    function applyRule (expression, axioms, action) {
        for (let i = 0; i < axioms.length; i++) {
            const [left, right] = axioms [i];
            const match = action === 'reduce' ? left : right;
            const replacer = action === 'reduce' ? right : left;
            const rewriteFound = expression._tryReplace (match, replacer);
            if (rewriteFound) {
                return {
                    result: rewriteFound,
                    axiom: `axiom_${i + 1}.0`,
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
        lineNumbers.innerHTML = lines.map ((_, index) => index + 1).join ('<br>');
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