try {

    /** Benchmark 25ms (test case 246) */

    let _input = document.getElementById ('input');
    let _output = document.getElementById ('output');
    let _lineNumbers = document.getElementById ('line-numbers');

    function solveProblem () {
        const { axioms, proofStatement, equivalences } = parseInput (_input.value);
        const startTime = performance.now ();
        _output.value = generateProof (axioms, proofStatement, equivalences);
        _output.value += `\n\nTotal runtime: ${ (performance.now ()-startTime).toFixed(4) } Milliseconds`;
    } // end solveProblem

    function parseInput (input) {
        let lines = input
            .split ('\n')
                .filter (line => line.trim () && !line.startsWith ('//'));
        
        let all_axioms = [];
        let equivalences = [];

        lines
            .slice ()
                .forEach ((line,k,thisArray) => {
                    const axiomID = `axiom_${k+1}.0`;

                    // Check if the line is a pure, symmetric equivalence rule
                    const hasEquiv = line.match(/\<==|==\>/g);
                    const hasOtherOps = line.includes('=');

                    // This is a standard axiom line for the reduce/expand engine
                    const parts = line.split(/[~<]?=+[>]?/g).map(s => s.trim());
                    parts.forEach((part, i) => {
                        parts.slice(i + 1).forEach((otherPart, j) => {
                            //if (!hasEquiv && hasOtherOps)
                                all_axioms.push({ subnets: `${part} = ${otherPart}`, axiomID: axiomID, guidZ: k });
                            //else if (hasEquiv && !hasOtherOps)
                             //   equivalences.push({ from: part, to: otherPart, id: axiomID });
                        });
                    });
                });

        const sortedAxioms = all_axioms
            .map (axiom => {
                axiom.subnets = axiom.subnets
                    .split (' = ')
                        .sort ((a, b) => a.length <= b.length)
                            .map ((pair,i,me) => {
                                return pair.match (/\S+/g);
                            });
                return axiom;
            });

        const proofStatement = sortedAxioms [sortedAxioms.length - 1];

        return {
            axioms: sortedAxioms,
            proofStatement: proofStatement,
            equivalences: equivalences
        };

    } // end parseInput
    
    function generateProof (all_axioms, proofStatement, equivalences) {
        let [lhs, rhs] = proofStatement.subnets;

        let LHS_PartialProofStack = [];
        let RHS_PartialProofStack = [];

        localStorage.setItem('LHS_PartialProofStack', '[]');
        localStorage.setItem('RHS_PartialProofStack', '[]');

        class CommitEntryCl {
            constructor({ gIDW = '', commit = [] }={}) {
                this.gIDW = gIDW;
                this.commit = commit;
            }
        } // end CommitEntryCl

        const proofFound = (() => {

            // Use core axioms only //
            let axioms = [...all_axioms];
            axioms.pop();

            let reduce_lhs_queue = [[...lhs]];
            let reduce_rhs_queue = [[...rhs]];
            let expand_lhs_queue = [[...lhs]];
            let expand_rhs_queue = [[...rhs]];
            let reduce_lhs_commit_history_map = new Map();
            let reduce_rhs_commit_history_map = new Map();
            let expand_lhs_commit_history_map = new Map();
            let expand_rhs_commit_history_map = new Map();
            let proofFoundFlag = (lhs.join (' ') == rhs.join (' '));
            
            // local scope to prevent naming collisions
            let w, x, y, z, w2, x2, y2, z2;

            const axiom_reduce_lhs = axiom_rewrite('reduce', axioms, 'lhs');
            const axiom_reduce_rhs = axiom_rewrite('reduce', axioms, 'rhs');
            const axiom_expand_lhs = axiom_rewrite('expand', axioms, 'lhs');
            const axiom_expand_rhs = axiom_rewrite('expand', axioms, 'rhs');

            const equiv_rewrite_reduce_lhs = equiv_rewrite('rewrite', equivalences, 'lhs');
            const equiv_rewrite_reduce_rhs = equiv_rewrite('rewrite', equivalences, 'rhs');
            const equiv_rewrite_expand_lhs = equiv_rewrite('rewrite', equivalences, 'lhs');
            const equiv_rewrite_expand_rhs = equiv_rewrite('rewrite', equivalences, 'rhs');

            // prime generators

            axiom_reduce_lhs?.next();
            axiom_reduce_rhs?.next();
            axiom_expand_lhs?.next();
            axiom_expand_rhs?.next();

            equiv_rewrite_reduce_lhs?.next();
            equiv_rewrite_reduce_rhs?.next();
            equiv_rewrite_expand_lhs?.next();
            equiv_rewrite_expand_rhs?.next();

            do {
                LHS_PartialProofStack = JSON.parse(localStorage.getItem('LHS_PartialProofStack'));
                RHS_PartialProofStack = JSON.parse(localStorage.getItem('RHS_PartialProofStack'));
                w = axiom_reduce_lhs?.next({
                        queue: reduce_lhs_queue,
                        commit_map: reduce_lhs_commit_history_map,
                        partial_proof_stack_: LHS_PartialProofStack,
                        proofFound_: proofFoundFlag
                    })?.value;
                LHS_PartialProofStack = JSON.parse(localStorage.getItem('LHS_PartialProofStack'));
                x = axiom_reduce_rhs?.next({
                        queue: reduce_rhs_queue,
                        commit_map: reduce_rhs_commit_history_map,
                        partial_proof_stack_: RHS_PartialProofStack,
                        proofFound_: proofFoundFlag
                    })?.value;
                RHS_PartialProofStack = JSON.parse(localStorage.getItem('RHS_PartialProofStack'));
                y = axiom_expand_lhs?.next({
                        queue: expand_lhs_queue,
                        commit_map: expand_lhs_commit_history_map,
                        partial_proof_stack_: LHS_PartialProofStack,
                        proofFound_: proofFoundFlag
                    })?.value;
                LHS_PartialProofStack = JSON.parse(localStorage.getItem('LHS_PartialProofStack'));
                z = axiom_expand_rhs?.next({
                        queue: expand_rhs_queue,
                        commit_map: expand_rhs_commit_history_map,
                        partial_proof_stack_: RHS_PartialProofStack,
                        proofFound_: proofFoundFlag
                    })?.value;
                RHS_PartialProofStack = JSON.parse(localStorage.getItem('RHS_PartialProofStack'));

                w2 = equiv_rewrite_reduce_lhs?.next({
                        queue: reduce_lhs_queue,
                        commit_map: reduce_lhs_commit_history_map,
                        partial_proof_stack_: LHS_PartialProofStack,
                        proofFound_: proofFoundFlag
                    })?.value;
                LHS_PartialProofStack = JSON.parse(localStorage.getItem('LHS_PartialProofStack'));
                x2 = equiv_rewrite_reduce_rhs?.next({
                        queue: reduce_rhs_queue,
                        commit_map: reduce_rhs_commit_history_map,
                        partial_proof_stack_: RHS_PartialProofStack,
                        proofFound_: proofFoundFlag
                    })?.value;
                RHS_PartialProofStack = JSON.parse(localStorage.getItem('RHS_PartialProofStack'));
                y2 = equiv_rewrite_expand_lhs?.next({
                        queue: expand_lhs_queue,
                        commit_map: expand_lhs_commit_history_map,
                        partial_proof_stack_: LHS_PartialProofStack,
                        proofFound_: proofFoundFlag
                    })?.value;
                LHS_PartialProofStack = JSON.parse(localStorage.getItem('LHS_PartialProofStack'));
                z2 = equiv_rewrite_expand_rhs?.next({
                        queue: expand_rhs_queue,
                        commit_map: expand_rhs_commit_history_map,
                        partial_proof_stack_: RHS_PartialProofStack,
                        proofFound_: proofFoundFlag
                    })?.value;
                RHS_PartialProofStack = JSON.parse(localStorage.getItem('RHS_PartialProofStack'));

            } while (!allComplete(w, x, y, z, w2, x2, y2, z2));

            return proofFoundFlag;

            function allComplete(...vals) {
                for (let val of vals) {
                    if (val == 1)
                        return false;
                }
                return true;
            } // end allComplete

            function* axiom_rewrite(action, _axioms_, side) {

                // const params = { queue: [], commit_map: new Map(), partial_proof_stack_: [], proofFound_: false,  };

                while (1) {
                    const params = yield;

                    if (!params || params.queue.length < 1){
                        yield 0;
                        continue;
                    }

                    if (!!params.proofFound_)
                        break;

                    const original_expr = params.queue.shift();

                    let noRewritesFlag = true;

                    for (let axiom of _axioms_) {
                        let tmp = [...original_expr];
                        const from = action === 'reduce' ? [...axiom.subnets[0]] : [...axiom.subnets[1]];
                        const to = action === 'reduce' ? [...axiom.subnets[1]] : [...axiom.subnets[0]];
                        const rewriteFoundFlag_A = tmp._tryReplace_A(from, to);
                        const rewriteFoundFlag_B = tmp._tryReplace_B(from, to);
                        if (rewriteFoundFlag_A) {
                            noRewritesFlag = false;
                            processNewRewrite(rewriteFoundFlag_A, side, action, axiom.axiomID, params, original_expr);
                            if (!!!params.proofFound_){
                                yield 1;
                            } else {
                                proofFoundFlag = params.proofFound_;
                                return 0;
                            }
                        }
                        if (rewriteFoundFlag_B) {
                            noRewritesFlag = false;
                            processNewRewrite(rewriteFoundFlag_B, side, action, axiom.axiomID, params, original_expr);
                            if (!!!params.proofFound_){
                                yield 1;
                            } else {
                                proofFoundFlag = params.proofFound_;
                                return 0;
                            }
                        }
                    }

                    if (noRewritesFlag) {
                        yield 0;
                    }

                }
                // no rewrite was performed //
                yield 0
            }

            function* equiv_rewrite(action, _equivalences_, side) {

                // const params = { queue: [], commit_map: new Map(), partial_proof_stack_: [], proofFound_: false };

                while (1) {
                    const params = yield;

                    if (!params || params.queue.length < 1){
                        yield 0;
                        continue;
                    }

                    if (!!params.proofFound_)
                        break;

                    let noRewritesFlag = true;
                    const _side_ = params.queue.shift();
                    for (let i = 0; i < _side_.length; i++) {
                        for (const equiv of _equivalences_) {
                            const token = _side_[i];
                            
                            // Forward rewrite: from -> to
                            if (token.startsWith(equiv.from)) {
                                const suffix = token.substring(equiv.from.length);
                                const newToken = equiv.to + suffix;
                                const new_expr = [..._side_.slice(0, i), newToken, ..._side_.slice(i + 1)];
                                processNewRewrite(new_expr, side, action, equiv.id, params, original_expr);
                                if (!!!params.proofFound_){
                                    noRewritesFlag = false;
                                    yield 1;
                                } else {
                                    proofFoundFlag = params.proofFound_;
                                    return 0;
                                }
                            }

                            // Backward rewrite: to -> from
                            if (token.startsWith(equiv.to)) {
                                const suffix = token.substring(equiv.to.length);
                                const newToken = equiv.from + suffix;
                                const new_expr = [..._side_.slice(0, i), newToken, ..._side_.slice(i + 1)];
                                processNewRewrite(new_expr, side, action, equiv.id, params, original_expr);
                                if (!!!params.proofFound_){
                                    noRewritesFlag = false;
                                    yield 1;
                                } else {
                                    proofFoundFlag = params.proofFound_;
                                    return 0;
                                }
                            }
                        }
                    }

                    if (noRewritesFlag) {
                        yield 0;
                    }
                }
                // no rewrite was performed //
                yield 0
            }
            
            function processNewRewrite(new_expr_array, side, action, via_id, state, original_expr) {

                // const state = { queue: [], commit_map: new Map(), partial_proof_stack_: [], proofFound_: false };

                const new_rewrite_str = new_expr_array.join(' ');

                if (state.commit_map.has(new_rewrite_str))
                    return;

                const original_str = original_expr.join(' ');
                
                let commitHistory = [];
                if (state.commit_map.has(original_str)) {
                    commitHistory = [...state.commit_map.get(original_str).commitHistory];
                } else {
                     commitHistory.push(new CommitEntryCl({ gIDW: 'root', commit: (side === 'lhs' ? lhs : rhs) }));
                }

                commitHistory.push(new CommitEntryCl({ gIDW: `${side} ${action} via ${via_id}`, commit: [...new_expr_array] }));
                
                state.commit_map.set(new_rewrite_str, { commitHistory });
                state.queue.push(new_expr_array);

                if (commitHistory.length > state.partial_proof_stack_.length) {
                    localStorage.setItem(((side == 'lhs') ? 'LHS_PartialProofStack' : 'RHS_PartialProofStack'), JSON.stringify(commitHistory, ' ', 2)) 
                }

                const other_maps = side === 'lhs' ? [reduce_rhs_commit_history_map, expand_rhs_commit_history_map] : [reduce_lhs_commit_history_map, expand_lhs_commit_history_map];
                for (const other_map of other_maps) {
                    if (other_map.has(new_rewrite_str)) {
                        const lhsCommits = side === 'lhs' ? commitHistory : other_map.get(new_rewrite_str).commitHistory;
                        const rhsCommits = side === 'rhs' ? commitHistory : other_map.get(new_rewrite_str).commitHistory;
                        state.proofFound_ = [lhsCommits, rhsCommits];
                    }
                }
            }

        })();

        LHS_PartialProofStack = JSON.parse(localStorage.getItem('LHS_PartialProofStack'));
        RHS_PartialProofStack = JSON.parse(localStorage.getItem('RHS_PartialProofStack'));

        if (!proofFound && (LHS_PartialProofStack.length < 1 && RHS_PartialProofStack.length < 1)) {
            return `No proof found.`;
        } else {
            const lambda_func = (u) => {
                let W = '';
                const _lhs_ = u[0]?.length ? u[0] : [new CommitEntryCl({ gIDW:'root', commit:lhs })] ;
                const _rhs_ = u[1]?.length ? u[1] : [new CommitEntryCl({ gIDW:'root', commit:rhs })] ;
                const _lhs_I = _lhs_.length;
                const _rhs_I = _rhs_.length;
                
                const finalLHS = _lhs_[_lhs_I - 1].commit.join(' ');
                const startRHS = _rhs_[0].commit.join(' ');

                // Print LHS path
                for(let i = 1; i < _lhs_I; i++) {
                    W += `${_lhs_[i].commit.join(' ')} = ${startRHS}, ${_lhs_[i].gIDW}\n`;
                }
                
                // Print RHS path
                for(let i = 1; i < _rhs_I; i++) {
                     W += `${finalLHS} = ${_rhs_[i].commit.join(' ')}, ${_rhs_[i].gIDW}\n`;
                }

                return W.trim();
            }
             const proofText = proofFound ? proofFound : [LHS_PartialProofStack, RHS_PartialProofStack];
             const firstStep = proofText[0][0];

             let proofString = `${( !proofFound ? 'Partial-' : '')}Proof Found!\n\n${firstStep.commit.join(' ')} = ${rhs.join(' ')}, ${firstStep.gIDW}\n`;
             proofString += lambda_func(proofText);
             
            return `${( !proofFound ? 'Partial-' : '')}Proof Found!\n\n${firstStep.commit.join(' ')} = ${rhs.join(' ')}, ${firstStep.gIDW}\n${lambda_func(proofText)}\n${( proofFound ? '\nQ.E.D.' : '' )}`;
        }

    } // end generateProof
     
    Array.prototype._tryReplace_A = function(from, to) {
        if (from.length > this.length)
          return false;
        
        let i = 0;
        let series = -1;
        let replaceSeries = [];
        const I = from.length;
        const J = this.length;
        const rewriteSZArray = [];
        let rewriteFoundFlag = false;
      
        for (let j = 0; j < J; ++j) {
            let _series_ = 0;    
            const tok = this[j];
            if (i < I && from[i] == tok) {
                if (!tok.match (/\{/) || (from[(i+1)] == this[(j+1)])){
                    _series_ = series;
                    if (++i == I) {
                        rewriteFoundFlag = true;
                        replaceSeries.push (j);
                        i = 0;
                    }
                }
            }
            rewriteSZArray.push({ series:_series_, tok:tok });
        }
        
        let ret = false;
        if (rewriteFoundFlag) {
            i = 0;
            ret = [];
            for (let o of rewriteSZArray) {
                if (o.series > -1 || (replaceSeries.length > 0 && i > replaceSeries[0])) {
                    ret.push (o.tok);                    
                } else if (replaceSeries.length > 0 && replaceSeries[0] == i) {
                    ret.push(...to);
                    replaceSeries.pop ();
                }
                ++i;
            }    
        }
        
        return ret;
    } // end Array.prototype._tryReplace_A
     
    Array.prototype._tryReplace_B = function(from, to) {
        if (from.length > this.length)
            return false;
        
        let i = 0;
        let series = 1;
        let replaceSeriesSet = new Set();
        const I = from.length;
        const J = this.length;
        const rewriteSZArray = [];
        let rewriteFoundFlag = false;
      
        for (let j = 0; j < J; ++j) {
            let _series_ = 0;    
            const tok = this[j];
            if (from[i] == tok) {
                _series_ = series;
                if (++i == I) {
                    i = 0;
                    rewriteFoundFlag = true;
                    replaceSeriesSet.add(series++);
                } // end if (++i == I)
            } // end if (from[i] == tok)
            rewriteSZArray.push({ series:_series_, tok:tok });
        }
        
        let ret = false;
        if (rewriteFoundFlag) {
            ret = [];
            let lastSeries = 0;
            for (let o of rewriteSZArray) {
                if (replaceSeriesSet.has (o.series)) {
                    if (o.series != lastSeries){
                        lastSeries = o.series;
                        ret.push(...to);
                    }
                } else {
                    ret.push (o.tok);
                }
            }    
        }
        
        return ret;
    } // end Array.prototype._tryReplace_B

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

// JavaScript: Persist textarea contents using localStorage

document.addEventListener('DOMContentLoaded', () => {
    const textarea = input;

    // Load saved value from localStorage if it exists
    const savedText = JSON.parse(localStorage.getItem('lastProof'));
    if (savedText !== null) {
        textarea.value = savedText;
    }

    // Save value to localStorage on input
    textarea.addEventListener('input', () => {
        localStorage.setItem('lastProof', JSON.stringify(textarea.value, ' ', 2));
    });
});

input.value = input.value ||
`// Axioms and Lemmas
1 + 1 = 2
2 + 2 = 4

// Prove
1 + 2 + 1 = 4`;

output.value = '';

updateLineNumbers ();