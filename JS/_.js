
try {

    function solveProblem() {
        const { axioms, proofStatement } = parseInput(document.getElementById('input').value);
        document.getElementById('output').value = generateProof(axioms, proofStatement);
    } // end solveProblem
    
    function parseInput(input) {
        const lines = input.split('\n').filter(line => line.trim() && !line.startsWith('//'));
        return {
            axioms: lines.slice(0, -1).map(line => line.split(/[~<]?=+[>]?/g).map(s => s.trim().split(/\s+/))),
            proofStatement: lines[lines.length - 1]
        };
    } // end parseInput
    
    function generateProof(axioms, proofStatement) {
        let [lhs, rhs] = proofStatement.split(/[~<]?=+[>]?/g).map(s => s.trim().split(/\s+/));
        let steps = [];
        let currentLhs = lhs, currentRhs = rhs;
    
        const applyRules = (side, action, current, other) => {
            const rule = action === 'reduce' ? tryReduce : tryExpand;
            let changed;
            do {
                changed = rule(current, axioms);
                if (changed) {
                    steps.push({ side, action, result: [...changed.result], axiom: changed.axiom, other: [...other] });
                    current = changed.result;
                }
            } while (changed && current.join(' ') != other.join(' '));
            return current;
        };
    
        currentRhs = applyRules('rhs', 'reduce', rhs, lhs);
        currentLhs = applyRules('lhs', 'reduce', lhs, rhs);
        
        if (currentLhs.join(' ') != currentRhs.join(' ')) {
            steps = [];
            currentRhs = applyRules('rhs', 'expand', rhs, lhs);
            currentLhs = applyRules('lhs', 'expand', lhs, rhs);
        }
    
        const proofFound = currentLhs.join(' ') === currentRhs.join(' ');
        let proof = `${proofFound ? 'Proof' : 'Partial-proof'} found!\n\n${proofStatement}, (root)\n`;
        steps.forEach(step => {
            proof += `${step.side === 'lhs' ? step.result.join(' ') : step.other.join(' ')} = ${step.side === 'lhs' ? step.other.join(' ') : step.result.join(' ')}, (${step.side} ${step.action}) via ${step.axiom}\n`;
        });
        return proof + (proofFound ? '\nQ.E.D.' : '');
    } // end generateProof
    
    Object.prototype._includes = function (indir) {
        let ret = false;
        const self = this;
        if (self.length >= indir.length){
            let i = 0;
            for (let tok of self) {
                if (indir [i] === tok)
                    ++i;
                !ret && (ret = (indir.length == i));
                if (ret)
                    break;
            }
        }
        return ret;
    }
    
    Object.prototype._replace = function (from, to) {
        let ret = false;
        let self = [...this];
        if (self.length >= from.length){
            let i = 0;
            let j = 0;
            let tokenIDX = [];
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
                }
                ++j;
            }
        }
        self = self.join (' ').split (/\s+/).filter (u => u).map ((s,index,me) => s.trim ());
        return self;
    }
    
    function tryReduce(expression, axioms) {
        return applyRule(expression, axioms, (left, right) => {
                let ret;
                expression._includes(left) && (ret = 'tryReduce');
                return ret;
            });
    } // end tryReduce
    
    function tryExpand(expression, axioms) {
        return applyRule(expression, axioms, (left, right) => {
                let ret;
                expression._includes(right) && (ret = 'tryExpand');
                return ret;
            });
    } // end tryExpand
    
    function applyRule(expression, axioms, condition) {
        for (let i = 0; i < axioms.length; i++) {
            const [left, right] = axioms[i];
            const indir = condition(left, right);
            if (indir) {
                return {
                    result: expression._replace(
                        indir === 'tryReduce'  ? left  : right , 
                        indir === 'tryReduce'  ? right : left ),
                    axiom: `axiom_${i + 1}.0`,
                };
            }
        }
        return null;
    } // applyRule
    
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