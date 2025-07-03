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
                    const hasEquiv = line.includes('<==>');
                    const hasOtherOps = line.includes('=') || line.includes('==>') || line.includes('<==');

                    if (hasEquiv && !hasOtherOps) {
                        // This line is for the rewrite engine
                        const parts = line.split('<==>').map(s => s.trim());
                        parts.forEach((part, i) => {
                            parts.slice(i + 1).forEach((otherPart, j) => {
                                equivalences.push({ from: part, to: otherPart, id: axiomID });
                            });
                         });
                    } else {
                        // This is a standard axiom line for the reduce/expand engine
                        const parts = line.split(/[~<]?=+[>]?/g).map(s => s.trim());
                        parts.forEach((part, i) => {
                            parts.slice(i + 1).forEach((otherPart, j) => {
                                all_axioms.push({ subnets: `${part} = ${otherPart}`, axiomID: axiomID, guidZ: k });
                            });
                        });
                    }
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
            let v, w, x, y, z, v2, w2, x2, y2, z2;

            const axiom_reduce_lhs = axiom_LHS('reduce', axioms, reduce_lhs_queue, reduce_lhs_commit_history_map, LHS_PartialProofStack, 'lhs');
            const axiom_reduce_rhs = axiom_LHS('reduce', axioms, reduce_rhs_queue, reduce_rhs_commit_history_map, RHS_PartialProofStack, 'rhs');
            const axiom_expand_lhs = axiom_LHS('expand', axioms, expand_lhs_queue, expand_lhs_commit_history_map, LHS_PartialProofStack, 'lhs');
            const axiom_expand_rhs = axiom_LHS('expand', axioms, expand_rhs_queue, expand_rhs_commit_history_map, RHS_PartialProofStack, 'rhs');

            const equiv_rewrite_lhs = equiv_LHS('rewrite', equivalences, reduce_lhs_queue, reduce_lhs_commit_history_map, LHS_PartialProofStack, 'lhs');
            const equiv_rewrite_rhs = equiv_LHS('rewrite', equivalences, reduce_rhs_queue, reduce_rhs_commit_history_map, RHS_PartialProofStack, 'rhs');
            const equiv_rewrite_expand_lhs = equiv_LHS('rewrite', equivalences, expand_lhs_queue, expand_lhs_commit_history_map, LHS_PartialProofStack, 'lhs');
            const equiv_rewrite_expand_rhs = equiv_LHS('rewrite', equivalences, expand_rhs_queue, expand_rhs_commit_history_map, RHS_PartialProofStack, 'rhs');

            do {
                if (proofFoundFlag) break;

                w = axiom_reduce_lhs?.next()?.value;
                x = axiom_reduce_rhs?.next()?.value;
                y = axiom_expand_lhs?.next()?.value;
                z = axiom_expand_rhs?.next()?.value;

                w2 = equiv_rewrite_lhs?.next()?.value;
                x2 = equiv_rewrite_rhs?.next()?.value;
                y2 = equiv_rewrite_expand_lhs?.next()?.value;
                z2 = equiv_rewrite_expand_rhs?.next()?.value;

            } while (!allComplete(w, x, y, z, w2, x2, y2, z2));

            return proofFoundFlag;

            function allComplete(...vals) {
                for (let val of vals) {
                    if (val == 1)
                        return false;
                }
                return true;
            } // end allComplete

            function* axiom_LHS(action, _axioms_, queue, commit_map, partial_proof_stack, side) {
                 while (1) {
                    if (proofFoundFlag || queue.length < 1) return 0;
                    const _side_ = queue.shift();
                    for (let axiom of _axioms_) {
                        let tmp = [..._side_];
                        const from = action === 'reduce' ? [...axiom.subnets[0]] : [...axiom.subnets[1]];
                        const to = action === 'reduce' ? [...axiom.subnets[1]] : [...axiom.subnets[0]];
                        const rewriteFoundFlag = tmp._tryReplace(from, to);
                        if (rewriteFoundFlag) {
                            processNewRewrite(rewriteFoundFlag, side, action, axiom.axiomID, commit_map, queue, partial_proof_stack, _side_);
                            if (proofFoundFlag) return 1;
                            yield 1;
                        }
                    }
                }
            }

            function* equiv_LHS(action, _equivalences_, queue, commit_map, partial_proof_stack, side) {
                while(1) {
                    if (proofFoundFlag || queue.length < 1) return 0;
                    const _side_ = queue.shift();
                    for (let i = 0; i < _side_.length; i++) {
                        for (const equiv of _equivalences_) {
                            const token = _side_[i];
                            
                            // Forward rewrite: from -> to
                            if (token.startsWith(equiv.from)) {
                                const suffix = token.substring(equiv.from.length);
                                const newToken = equiv.to + suffix;
                                const new_expr = [..._side_.slice(0, i), newToken, ..._side_.slice(i + 1)];
                                processNewRewrite(new_expr, side, action, equiv.id, commit_map, queue, partial_proof_stack, _side_);
                                if (proofFoundFlag) return 1;
                                yield 1;
                            }

                            // Backward rewrite: to -> from
                            if (token.startsWith(equiv.to)) {
                                const suffix = token.substring(equiv.to.length);
                                const newToken = equiv.from + suffix;
                                const new_expr = [..._side_.slice(0, i), newToken, ..._side_.slice(i + 1)];
                                processNewRewrite(new_expr, side, action, equiv.id, commit_map, queue, partial_proof_stack, _side_);
                                if (proofFoundFlag) return 1;
                                yield 1;
                            }
                        }
                    }
                }
            }
            
            function processNewRewrite(new_expr_array, side, action, via_id, commit_map, queue, partial_proof_stack, original_expr) {
                const new_rewrite_str = new_expr_array.join(' ');
                if (commit_map.has(new_rewrite_str)) return;

                const original_str = original_expr.join(' ');
                
                let commitHistory = [];
                if (commit_map.has(original_str)) {
                    commitHistory = [...commit_map.get(original_str).commitHistory];
                } else {
                     commitHistory.push(new CommitEntryCl({ gIDW: 'root', commit: (side === 'lhs' ? lhs : rhs) }));
                }

                commitHistory.push(new CommitEntryCl({ gIDW: `${side} ${action} via ${via_id}`, commit: [...new_expr_array] }));
                
                commit_map.set(new_rewrite_str, { commitHistory });
                queue.push(new_expr_array);

                if (commitHistory.length > partial_proof_stack.length) {
                    partial_proof_stack = commitHistory;
                }

                const other_maps = side === 'lhs' ? [reduce_rhs_commit_history_map, expand_rhs_commit_history_map] : [reduce_lhs_commit_history_map, expand_lhs_commit_history_map];
                for (const other_map of other_maps) {
                    if (other_map.has(new_rewrite_str)) {
                        const lhsCommits = side === 'lhs' ? commitHistory : other_map.get(new_rewrite_str).commitHistory;
                        const rhsCommits = side === 'rhs' ? commitHistory : other_map.get(new_rewrite_str).commitHistory;
                        proofFoundFlag = [lhsCommits, rhsCommits];
                        return;
                    }
                }
            }

        })();

        if (!proofFound && LHS_PartialProofStack.length < 1 && RHS_PartialProofStack.length < 1) {
            return `No proof found.`;
        } else {
            const lambda_func = (u) => {
                let W = '';
                const _lhs_ = u[0]?.length ? u[0] : [new CommitEntryCl({ gIDW:'root', commit:lhs })] ;
                const _rhs_ = u[1]?.length ? u[1] : [new CommitEntryCl({ gIDW:'root', commit:rhs })] ;
                const _lhs_I = _lhs_.length;
                const _rhs_I = _rhs_.length;
                
                const finalLHS = _lhs_[_lhs_I - 1].commit.join(' ');
                const finalRHS = _rhs_[_rhs_I - 1].commit.join(' ');

                const meetingPoint = finalLHS; 

                // Print LHS path
                for(let i = 1; i < _lhs_I; i++) {
                    W += `${_lhs_[i].commit.join(' ')} = ${finalRHS}, ${_lhs_[i].gIDW}\n`;
                }
                
                // Print RHS path
                const rhs_path_reversed = [..._rhs_].reverse();
                for(let i = 1; i < _rhs_I; i++) {
                     W += `${finalLHS} = ${rhs_path_reversed[i].commit.join(' ')}, ${rhs_path_reversed[i].gIDW}\n`;
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
     
    Array.prototype._tryReplace = function(from, to) {
        if (from.length > this.length)
          return false;
      
        class keyCL {
          constructor({ series=0, tok='' }={}) {
            this.series = series;
            this.tok = tok;
          }
        } // end class
        
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
            if (i < I && from[i] == tok) {
                _series_ = series;
                if (++i == I) {
                    i = 0;
                    rewriteFoundFlag = true;
                    replaceSeriesSet.add(series++);
                }
            }
            rewriteSZArray.push(new keyCL({ series:_series_, tok:tok }) );
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
            }
            else {
              ret.push (o.tok);
            }
          }    
        }
        
        return ret;
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

updateLineNumbers ();