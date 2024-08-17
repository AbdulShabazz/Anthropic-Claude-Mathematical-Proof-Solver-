
try {

    /** Benchmark 4ms (test case 246) */

    let _input = document.getElementById ('input');
    let _output = document.getElementById ('output');
    let _lineNumbers = document.getElementById ('line-numbers');

    class SubnetClass extends Array {
        constructor(){
            super();
            let self = this;
            self._lhsReduce = [];
            self._lhsExpand = [];
            self._rhsReduce = [];
            self._rhsExpand = [];
        }
    } // end SubnetClass

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
        let axioms = new Set ();

        lines
            .slice (0/* , -1 */)
                .forEach ((line,k,thisArray) => {
                    const parts = line
                        .split (/[~<]?=+[>]?/g)
                            .map (s => s.trim ());
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
            
            for (let i = 0; i < I; i++) {
                for (let j = i; j < I; j++) {
                    if (i == j) continue ;
                    // axioms
                    let lhsAxiom = unsortedAxiomsArray [i];
                    let rhsAxiom = unsortedAxiomsArray [j];
                    let [ lhsAxiomLHS, lhsAxiomRHS ] = lhsAxiom.subnets;
                    let [ rhsAxiomLHS, rhsAxiomRHS ] = rhsAxiom.subnets;
                    buildSubnetCallGraphF (lhsAxiom, j, rhsAxiomLHS, 'lhs');
                    buildSubnetCallGraphF (lhsAxiom, j, rhsAxiomRHS, 'rhs');
                    buildSubnetCallGraphF (rhsAxiom, i, lhsAxiomLHS, 'lhs');
                    buildSubnetCallGraphF (rhsAxiom, i, lhsAxiomRHS, 'rhs');
                }
            } // end for (let i = 0; i < I; i++) 

        } // end buildSubnetCallGraphs (...)

        function buildSubnetCallGraphF (axiom, i, from, indirectionSZ) {
            let [ lhs, rhs ] = axiom.subnets;
            const ci_lhsZ = lhs._genConfidenceInterval (from);
            const ci_rhsZ = rhs._genConfidenceInterval (from);
            const subnetReduceFlag = Boolean(/^lhs/.test(indirectionSZ));
            if (ci_lhsZ && subnetReduceFlag) {
                AddToLHSReduceSubnet (axiom, i);
            } else if (ci_lhsZ) {                
                AddToLHSExpandSubnet (axiom, i);
            } 
            if (ci_rhsZ && subnetReduceFlag) {
                AddToRHSReduceSubnet (axiom, i);
            } else if (ci_rhsZ) {         
                AddToRHSExpandSubnet (axiom, i);
            }
        } // end buildSubnetCallGraphF (axiom, from, to)

        function AddToLHSReduceSubnet (axiom, i) {
            !axiom._lhsReduce && (axiom._lhsReduce = []);
            axiom._lhsReduce.push (i);
        } // end AddToLHSReduceSubnet

        function AddToLHSExpandSubnet (axiom, i) {
            !axiom._lhsExpand && (axiom._lhsExpand = []);
            axiom._lhsExpand.push (i);
        } // end AddToLHSExpandSubnet

        function AddToRHSReduceSubnet (axiom, i) {
            !axiom._rhsReduce && (axiom._rhsReduce = []);
            axiom._rhsReduce.push (i);
        } // end AddToRHSReduceSubnet

        function AddToRHSExpandSubnet (axiom, i) {
            !axiom._rhsExpand && (axiom._rhsExpand = []);
            axiom._rhsExpand.push (i);
        } // end AddToRHSExpandSubnet

    } // end parseInput

    function generateProof (axioms, proofStatement) {
        let steps = [];
        let [lhs, rhs] = proofStatement.subnets;
        const proofFound = (() => {
            if (lhs.join (' ') == rhs.join (' '))
                return true;
            let ret = applyRules (proofStatement.axiomID, [[...lhs], [...rhs]],'reduce');
            ret == (lhs.join (' ') == rhs.join (' '));
            !ret && (steps = []) && (ret = applyRules (proofStatement.axiomID, [[...lhs], [...rhs]], 'expand'));
            return ret;
        })();

        return `${proofFound ? 'Proof' : 'Partial-proof'} found!\n\n${proofStatement.subnets [0].join (' ')} = ${proofStatement.subnets [1].join (' ')}, (root)\n` +
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

        function applyRules (axiomID, sides, action) {
            sides = sides.map ((current,idx,me) => {
                let changed;
                const side = idx == 0 ? 'lhs' : 'rhs' ;
                do {
                    changed = applyRule (axiomID, side, current, axioms, action);
                    if (changed) {
                        steps.push ({ side, action, result: [...changed.result], axiomID: changed.axiomID, other: [] });
                        current = changed.result;
                        axiomID = changed.axiomRewriteID;
                    }
                } while (changed);
                return current;
            });
            return (sides [0].join (' ') == sides [1].join (' '));
        } // end applyRules

    } // end generateProof

    function applyRule (axiomID, side, expression, axioms, action) {
        //const I = axioms.length;
        const guidZ = (Number(axiomID) === axiomID )
            ? axiomID 
            : Number(axiomID.match(/(\d+)/)[0]) - 1 ;
        const axiomIDS = (() => {
            let tmpA = [];
            switch (action) {
                case 'reduce': 
                    if (axioms [guidZ]?._lhsReduce && side === 'lhs') {
                        tmpA.push (...axioms [guidZ]?._lhsReduce);
                    } else if (axioms [guidZ]?._rhsReduce && side === 'rhs') {
                        tmpA.push (...axioms [guidZ]?._rhsReduce);
                    }
                    break;
                case 'expand':
                    if (axioms [guidZ]?._lhsExpand && side === 'lhs') {
                        tmpA.push (...axioms [guidZ]?._lhsExpand);
                    } else if (axioms [guidZ]?._rhsExpand && side === 'rhs') {
                        tmpA.push (...axioms [guidZ]?._rhsExpand);
                    }
                    break;
            } // end switch (action)
            return tmpA;
        }) ();
        for (let i = axiomIDS.shift (); axiomIDS.length > 0; i = axiomIDS.shift ()) {
            if (i == guidZ) continue;
            const axiom = axioms [i];
            const [left, right] = axiom.subnets;
            const from = action === 'reduce' ? left : right;
            const to = action === 'reduce' ? right : left;
            const rewriteFound = expression._tryReplace (from, to);
            if (rewriteFound) {
                return {
                    result: rewriteFound,
                    axiomID: axiom.axiomID,
                    axiomRewriteID: i,
                };
            }
        }
        return null;
    } // end applyRule

    Object.prototype._tryReplace = function(from, to) {
        if (from.length > this.length) return false;

        let i = 0;
        const I = from.length;
        const J = this.length;
        const rewriteSZArray = [];
        let rewriteFoundFlag = false;
        const boundScopeSatisfied = (tok,j,i) =>
            from[i] == this[j]
                && this._scope_satisfied(tok, this, j, from, i);

        for (let j = 0; j < J; j++) {
            const tok = this [j];
            if (boundScopeSatisfied (tok, j, i)) {
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

    Object.prototype._genConfidenceInterval = function(from) {
        if (from.length > this.length) return false;

        let i = 0;
        const I = from.length;
        const J = this.length;
        let confidenceIntervalZ = 0;;
        const boundScopeSatisfied = (tok,j,i) =>
            from[i] == this[j]
                && ++confidenceIntervalZ
                    && this._scope_satisfied(tok, this, j, from, i);

        for (let j = 0; j < J; j++) {
            const tok = this [j];
            if (boundScopeSatisfied (tok, j, i)
                        && (++i === I)) {
                    i = 0;
            } 
        }

        return confidenceIntervalZ;
    } // end Object.prototype._genConfidenceInterval

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
