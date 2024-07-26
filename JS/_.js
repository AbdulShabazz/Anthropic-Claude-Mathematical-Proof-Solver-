
/*

    TITLE:
    Experimental-Parser.js

    AUTHOR: Seagat2011
    http://eterna.cmu.edu/web/player/90270/
    http://fold.it/port/user/1992490

    VERSION:
    Major.Minor.Release.Build
    0.0.1.0

    DESCRIPTION:
    claude AI based Experimental Prover

    UPDATES
    N/A

    TODOS
    More Flexable axiom parsing via Map builtin objects
    Rewrite queue for more variance and (solution space) coverage
    Add Multi-thread support via inline Web Workers
    Add async/await and Promise.All support

    STYLEGUIDE:
    http://google-styleguide.googlecode.com/svn/trunk/javascriptguide.xml

    EXAMPLE:
    const ProofStatementA = [
        // Axioms and Lemmas
        "1 + 1 = 2",
        "2 + 2 = 4",
        // Theorem to prove
        "1 + 2 + 1 = 4",
    ];

    SCRIPT TYPE:
    Euclid Tool

*/

try {

    function solveProblem () {
        let rewriteQueue = [];
        const input = document.getElementById ('input').value;
        const output = document.getElementById ('output');
        const { axioms, proofStatement } = parseInput (input);
        const proof = generateProof (axioms, proofStatement, rewriteQueue);
        output.value = proof;
    }
    
    function parseInput (input) {
        const lines = input.split ('\n').map (line => line.trim ()).filter (line => line && !line.startsWith ('//'));
        const axioms = [];
        let proofStatement = '';
        const isProof = lines.length-1;
        lines.forEach ((line, indexZ, thisArray) => {
            if (indexZ != isProof) {
                line = line.split (/[~<]?=+[>]?/g).map (s => s.trim ());
                const _lhs = line [0].split (/\s+/g).map (s => s.trim ());
                const _rhs = line [1].split (/\s+/g).map (s => s.trim ());
                axioms.push ([
                    _lhs.length >= _rhs.length ? _lhs : _rhs,
                    _lhs.length >= _rhs.length ? _rhs : _lhs,
                ]);
            } else {
                proofStatement = line;
            }
        });
        return { axioms, proofStatement };
    }
    
    function generateProof (axioms, proofStatement, rewriteQueue) {
        let proof;
        let [lhs, rhs] = proofStatement.split (/[~<]?=+[>]?/g).map (s => s.trim ());
    
        if (lhs === rhs)
            return proof + `\nQ.E.D.`;
    
        lhs = lhs.split (/\s+/).map (s => s.trim ());
        rhs = rhs.split (/\s+/).map (s => s.trim ());
    
        let steps = [];
        let currentLhs;
        let currentRhs;
    
        currentLhs = lhs;
        currentRhs = rhs;
    
        // Try to reduce RHS first
        while (currentLhs.join (' ') !== currentRhs.join (' ')) {
            const rhsReduction = tryReduce (currentRhs, axioms);
            if (rhsReduction) {
                steps.push ({ side: 'rhs', action: 'reduce', result: [...rhsReduction.result], axiom: rhsReduction.axiom, other: [...currentLhs] });
                currentRhs = rhsReduction.result;
            } else {
                break;
            }
        }
    
        // If LHS and RHS are not equal, try reducing LHS
        while (currentLhs.join (' ') !== currentRhs.join (' ')) {
            const lhsReduction = tryReduce (currentLhs, axioms);
            if (lhsReduction) {
                steps.push ({ side: 'lhs', action: 'reduce', result: [...lhsReduction.result], axiom: lhsReduction.axiom, other: [...currentRhs] });
                currentLhs = lhsReduction.result;
                if (currentLhs === currentRhs) break;
            } else {
                break;
            }
        }
    
        if (currentLhs.join (' ') !== currentRhs.join (' ')) {
            currentLhs = lhs;
            currentRhs = rhs;
            steps = [];
        }
    
        // Then expand RHS
        while (currentLhs.join (' ') !== currentRhs.join (' ')) {
            const rhsReduction = tryExpand (currentRhs, axioms);
            if (rhsReduction) {
                steps.push ({ side: 'rhs', action: 'expand', result: [...rhsReduction.result], axiom: rhsReduction.axiom, other: [...currentLhs] });
                currentRhs = rhsReduction.result;
            } else {
                break;
            }
        }
    
        // Then expand LHS
        while (currentLhs.join (' ') !== currentRhs.join (' ')) {
            const lhsExpansion = tryExpand (currentLhs, axioms);
            if (lhsExpansion) {
                steps.push ({ side: 'lhs', action: 'expand', result: [...lhsExpansion.result], axiom: lhsExpansion.axiom, other: [...currentRhs] });
                currentLhs = lhsExpansion.result;
            } else {
                break;
            }
        }
    
        const ProofFound = (currentLhs.join (' ') == currentRhs.join (' '));
        const QED = (() => {
            let ret = '';
            if (ProofFound)
                ret = '\nQ.E.D.'
           return ret;
        })();
    
        proof = `${ProofFound ? 'Proof' : 'partial-proof'} found!\n\n${proofStatement}, (root)\n`;
    
        for (const step of steps) {
            switch (step.side) {
                case 'lhs':
                proof += `${ step.result.join (' ') } = ${ step.other.join (' ') }, (${ step.side } ${ step.action }) via ${ step.axiom }\n`;
                break;
    
                case 'rhs':
                proof += `${ step.other.join (' ') } = ${ step.result.join (' ') }, (${ step.side } ${ step.action }) via ${ step.axiom }\n`;
                break;
            }
        }
    
        proof += QED;
        return proof;
    }
    
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
    
    function tryReduce (expression, axioms) {
        for (let i = 0; i < axioms.length; i++) {
            const [left, right] = axioms [i];
            if (expression._includes (left)) {
                return {
                    result: expression._replace (left, right),
                    axiom: `axiom_${i + 1}.0`
                };
            }
        }
        return null;
    }
    
    function tryExpand (expression, axioms) {
        for (let i = 0; i < axioms.length; i++) {
            const [left, right] = axioms [i];
            if (expression._includes (right)) {
                return {
                    result: expression._replace (right, left),
                    axiom: `axiom_${i + 1}.0`
                };
            }
        }
        return null;
    }
    
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