
try {

    /** Benchmark 40ms (test case 246) */

    let _input = document.getElementById ('input');
    let _output = document.getElementById ('output');
    let _lineNumbers = document.getElementById ('line-numbers');

    function solveProblem () {
        rewriteHistoryProofFoundFlag = false;
        const { axioms, proofStatement } = parseInput (_input.value);
        const startTime = performance.now ();
        _output.value = generateProof (axioms, proofStatement);
        _output.value += `\n\nTotal runtime: ${ (performance.now ()-startTime).toFixed(4) } Milliseconds`;
    } // end solveProblem

    function parseInput (input) {
        let lines = input
            .split ('\n')
                .filter (line => line.trim () && !line.startsWith ('//'));
        let axiomsSet = new Set ();

        lines
            .slice ()
                .forEach ((line,k,thisArray) => {
                    const parts = line
                        .split (/[~<]?=+[>]?/g)
                            .map (s => s.trim ());
                    parts.forEach ((part, i) => {
                        parts.slice (i + 1).forEach ((otherPart, j, me) => {
                            axiomsSet.add ({ subnets: `${part} = ${otherPart}`, axiomID: `axiom_${k+1}.0` , guidZ: k });
                        });
                    });
                });

        const sortedAxioms = Array.from (axiomsSet)
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
            proofStatement: proofStatement
        };

    } // end parseInput

    function generateProof (all_axioms, proofStatement) {
        let [lhs, rhs] = proofStatement.subnets;
        const proofFound = (() => {
            class CommitEntryCl {
                constructor({ gIDW = '', commit = [] }={}) {
                    this.gIDW = gIDW;
                    this.commit = commit;
                }
            }

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
            let uVal;

            const uu = rewriteQueue(axioms);

            do {
                if (proofFoundFlag) break;

                // Advance each iterator and capture its .value
                uVal = uu?.next()?.value;

                // If all are 0 or NaN or undefined, we should stop.
                // Otherwise, keep looping.
            //} while (!allComplete(wVal, xVal, yVal, zVal));
            } while (!allComplete(uVal));

            return proofFoundFlag;

            function allComplete(...vals) {
                for (let val of vals) {
                    if (val == 1)
                        return false;
                }
                return true;
            } // end allComplete

            function* rewriteQueue(_axioms_) {
                while (1) {
                    const AllQueuesEmptyFlag =
                        (
                            reduce_lhs_queue.length < 1
                            && reduce_rhs_queue.length < 1
                            && expand_lhs_queue.length < 1
                            && expand_rhs_queue.length < 1
                        );
                    if (proofFoundFlag || AllQueuesEmptyFlag)
                        return 0;
                    const _reduce_lhs_ = reduce_lhs_queue.shift();
                    const _reduce_rhs_ = reduce_rhs_queue.shift();
                    const _expand_lhs_ = expand_lhs_queue.shift();
                    const _expand_rhs_ = expand_rhs_queue.shift();
                    for (let axiom of _axioms_) {
                        if (_reduce_lhs_) {
                            let tmp = [..._reduce_lhs_];
                            const curr_rewrite = `${_reduce_lhs_.join(' ')}`;
                            if (!reduce_lhs_commit_history_map.has(curr_rewrite)) {
                                reduce_lhs_commit_history_map
                                    .set(curr_rewrite, {
                                            alreadyReducedSet:new Set(),
                                            commitHistory:[ new CommitEntryCl({ gIDW:'root', commit:[...tmp] }) ]
                                        }
                                    );
                            }
                            const from = [...axiom.subnets[0]];
                            const to = [...axiom.subnets[1]];
                            const rewriteFoundFlag = tmp._tryReplace(from,to);
                            if (rewriteFoundFlag) {
                                //rewriteFoundFlag_reduce_lhs = true;
                                reduce_lhs_queue.push([...rewriteFoundFlag]);
                                const new_rewrite = rewriteFoundFlag.join(' ');
                                const commitHistory = [
                                    ...reduce_lhs_commit_history_map.get(curr_rewrite).commitHistory,
                                    new CommitEntryCl({ gIDW:`lhs reduce via ${axiom.axiomID}`, commit:[...rewriteFoundFlag] })
                                ];
                                let _alreadyReducedSet_ = new Set([ ...reduce_lhs_commit_history_map.get(curr_rewrite).alreadyReducedSet, axiom.axiomID ]);
                                reduce_lhs_commit_history_map.set(new_rewrite, {
                                    alreadyReducedSet:_alreadyReducedSet_,
                                    commitHistory:commitHistory
                                });
                                const _ProofFoundFlag_ = (reduce_rhs_commit_history_map.has(new_rewrite)
                                    || expand_rhs_commit_history_map.has(new_rewrite));
                                if (_ProofFoundFlag_)  {
                                    // Capture the LHS commit history once.
                                    const lhsCommits = reduce_lhs_commit_history_map.get(new_rewrite).commitHistory;
    
                                    // Determine which RHS map to use.
                                    const rhsMap = reduce_rhs_commit_history_map.has(new_rewrite)
                                        ? reduce_rhs_commit_history_map
                                        : expand_rhs_commit_history_map ;
    
                                    // Set the proofFoundFlag from both sides.
                                    proofFoundFlag = [
                                        [...lhsCommits],
                                        [...rhsMap.get(new_rewrite).commitHistory]
                                    ];
    
                                } // end if (_ProofFoundFlag_)
                                yield 1;
                            } // end if rewriteFoundFlag
                        } // end if _reduce_lhs_
                        if (_reduce_rhs_) {
                            let tmp = [..._reduce_rhs_];
                            const curr_rewrite = `${_reduce_rhs_.join(' ')}`;
                            if (!reduce_rhs_commit_history_map.has(curr_rewrite)) {
                                reduce_rhs_commit_history_map
                                    .set(curr_rewrite, {
                                            alreadyReducedSet:new Set(),
                                            commitHistory:[ new CommitEntryCl({ gIDW:'root', commit:[...tmp] }) ]
                                        }
                                    );
                            }
                            const from = [...axiom.subnets[0]];
                            const to = [...axiom.subnets[1]];
                            const rewriteFoundFlag = tmp._tryReplace(from,to);
                            if (rewriteFoundFlag) {
                                //rewriteFoundFlag_reduce_rhs = true;
                                reduce_rhs_queue.push([...rewriteFoundFlag]);
                                const new_rewrite = rewriteFoundFlag.join(' ');
                                const commitHistory = [
                                    ...reduce_rhs_commit_history_map.get(curr_rewrite).commitHistory,
                                    new CommitEntryCl({ gIDW:`rhs reduce via ${axiom.axiomID}`, commit:[...rewriteFoundFlag] })
                                ];
                                let _alreadyReducedSet_ = new Set([ ...reduce_rhs_commit_history_map.get(curr_rewrite).alreadyReducedSet, axiom.axiomID ]);
                                reduce_rhs_commit_history_map.set(new_rewrite, {
                                    alreadyReducedSet:_alreadyReducedSet_,
                                    commitHistory:commitHistory
                                });
                                const _ProofFoundFlag_ = (reduce_lhs_commit_history_map.has(new_rewrite)
                                    || expand_lhs_commit_history_map.has(new_rewrite));
                                if (_ProofFoundFlag_) {
                                    // Capture the RHS commit history once.
                                    const rhsCommits = reduce_rhs_commit_history_map.get(new_rewrite).commitHistory;
    
                                    // Determine which LHS map to use.
                                    const lhsMap = reduce_lhs_commit_history_map.has(new_rewrite)
                                        ? reduce_lhs_commit_history_map
                                        : expand_lhs_commit_history_map ;
    
                                    // Set the proofFoundFlag from both sides.
                                    proofFoundFlag = [
                                        [...lhsMap.get(new_rewrite).commitHistory],
                                        [...rhsCommits]
                                    ];
    
                                } // end if (_ProofFoundFlag_)
                                yield 1;
                            } // end if rewriteFoundFlag
                        } // end if _reduce_rhs_
                        if (_expand_lhs_) {
                            let tmp = [..._expand_lhs_];
                            const curr_rewrite = `${_expand_lhs_.join(' ')}`;
                            if (!expand_lhs_commit_history_map.has(curr_rewrite)) {
                                expand_lhs_commit_history_map
                                    .set(curr_rewrite, {
                                            alreadyExpandedSet:new Set(),
                                            commitHistory:[ new CommitEntryCl({ gIDW:'root', commit:[...tmp] }) ]
                                        }
                                    );
                            }
                            const from = [...axiom.subnets[1]];
                            const to = [...axiom.subnets[0]];
                            const rewriteFoundFlag = tmp._tryReplace(from,to);
                            if (rewriteFoundFlag) {
                                //rewriteFoundFlag_expand_lhs = true;
                                expand_lhs_queue.push([...rewriteFoundFlag]);
                                const new_rewrite = rewriteFoundFlag.join(' ');
                                const commitHistory = [
                                    ...expand_lhs_commit_history_map.get(curr_rewrite).commitHistory,
                                    new CommitEntryCl({ gIDW:`lhs expand via ${axiom.axiomID}`, commit:[...rewriteFoundFlag] })
                                ];
                                let _alreadyExpandedSet_ = new Set([ ...expand_lhs_commit_history_map.get(curr_rewrite).alreadyExpandedSet, axiom.axiomID ]);
                                expand_lhs_commit_history_map.set(new_rewrite, {
                                    alreadyExpandedSet:_alreadyExpandedSet_,
                                    commitHistory:commitHistory
                                });
                                const _ProofFoundFlag_ = (reduce_rhs_commit_history_map.has(new_rewrite)
                                    || expand_rhs_commit_history_map.has(new_rewrite));
                                if (_ProofFoundFlag_) {
                                    // Capture the LHS commit history once.
                                    const lhsCommits = expand_lhs_commit_history_map.get(new_rewrite).commitHistory;
    
                                    // Determine which RHS map to use.
                                    const rhsMap = reduce_rhs_commit_history_map.has(new_rewrite)
                                        ? reduce_rhs_commit_history_map
                                        : expand_rhs_commit_history_map ;
    
                                    // Set the proofFoundFlag from both sides.
                                    proofFoundFlag = [
                                        [...lhsCommits],
                                        [...rhsMap.get(new_rewrite).commitHistory]
                                    ];
    
                                } // end if (_ProofFoundFlag_)
                                yield 1;
                            } // end if rewriteFoundFlag
                        } // end if _expand_lhs_
                        if (_expand_rhs_) {
                            let tmp = [..._expand_rhs_];
                            const curr_rewrite = `${_expand_rhs_.join(' ')}`;
                            if (!expand_rhs_commit_history_map.has(curr_rewrite)) {
                                expand_rhs_commit_history_map
                                    .set(curr_rewrite, {
                                            alreadyExpandedSet:new Set(),
                                            commitHistory:[ new CommitEntryCl({ gIDW:'root', commit:[...tmp] }) ]
                                        }
                                    );
                            }
                            const from = [...axiom.subnets[1]];
                            const to = [...axiom.subnets[0]];
                            const rewriteFoundFlag = tmp._tryReplace(from,to);
                            if (rewriteFoundFlag) {
                                //rewriteFoundFlag_expand_rhs = true;
                                expand_rhs_queue.push([...rewriteFoundFlag]);
                                const new_rewrite = rewriteFoundFlag.join(' ');
                                const commitHistory = [
                                    ...expand_rhs_commit_history_map.get(curr_rewrite).commitHistory,
                                    new CommitEntryCl({ gIDW:`rhs expand via ${axiom.axiomID}`, commit:[...rewriteFoundFlag] })
                                ];
                                let _alreadyExpandedSet_ = new Set([ ...expand_rhs_commit_history_map.get(curr_rewrite).alreadyExpandedSet, axiom.axiomID ]);
                                expand_rhs_commit_history_map.set(new_rewrite, {
                                    alreadyExpandedSet:_alreadyExpandedSet_,
                                    commitHistory:commitHistory
                                });
                                const _ProofFoundFlag_ = (reduce_lhs_commit_history_map.has(new_rewrite)
                                    || expand_lhs_commit_history_map.has(new_rewrite));
                                if (_ProofFoundFlag_) {
                                    // Capture the RHS commit history once.
                                    const rhsCommits = expand_rhs_commit_history_map.get(new_rewrite).commitHistory;
    
                                    // Determine which LHS map to use.
                                    const lhsMap = reduce_lhs_commit_history_map.has(new_rewrite)
                                        ? reduce_lhs_commit_history_map
                                        : expand_lhs_commit_history_map ;
    
                                    // Set the proofFoundFlag from both sides.
                                    proofFoundFlag = [
                                        [...lhsMap.get(new_rewrite).commitHistory],
                                        [...rhsCommits]
                                    ];
    
                                } // end if (_ProofFoundFlag_)
                                yield 1;
                            } // end if rewriteFoundFlag
                        } // end if _expand_rhs_
                    } // end for (let axiom of _axioms_) 
                } // end while (1)
            } // end rewriteQueue

        })(); // end proofFound inline func

        if (!proofFound) {
            return `No proof found.`;
        }
        else {
            const lambda_func = (u) => {
                let W = '';
                const _lhs_ = u[0];
                const _rhs_ = u[1];
                const _lhs_I = u[0].length;
                const _rhs_I = u[1].length;
                const x = `${ _lhs_[ (_lhs_I-1) ].commit.join(' ') }`;
                const y = `${ _rhs_[0].commit.join(' ') }`;
                for (let i = 0; i < _lhs_I; ++i) {
                    const w = `${ _lhs_[i].commit.join(' ') }`;
                    const detailsW = `, ${ _lhs_[i].gIDW }`;
                    W += `${ w } = ${ y }${ detailsW }\n`;
                } // end for (let i = 0; i < _lhs_I; ++i) {
                for (let i = 1; i < _rhs_I; ++i) {
                    const w = `${ _rhs_[i].commit.join(' ') }`;
                    const detailsW = `, ${ _rhs_[i].gIDW }`;
                    W += `${ x } = ${ w }${ detailsW }\n`;
                } // end for (let i = 0; i < _rhs_I; ++i) {
                return W;
            } // end lambda_func
            return `Proof Found!\n\n${ lambda_func(proofFound) }\nQ.E.D.`;
        } // end if (!proofFound)

    } // end generateProof

    Object.prototype._tryReplace = function(from, to) {
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
            if (from[i] == tok) {
                _series_ = series;
                if (++i == I) {
                    i = 0;
                    rewriteFoundFlag = true;
                    replaceSeriesSet.add(series++);
                } // end if (++i == I)
            } // end if (from[i] == tok)
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
    } // end Object.prototype._tryReplace

    Object.prototype._scope_satisfied = function(tok, lhs, l, rhs, r) {
        if (lhs[l] !== rhs[r]) return false;

        const endScope = { "(": ")", "{": "}" };
        if (!(tok in endScope)) return { j : l };
        const endToken = endScope[tok];
        const I = rhs.length;
        const J = lhs.length;

        for (let i = 1; (r + i < I) && (l + i < J); i++) {
            const ltok = lhs[l + i];
            const rtok = rhs[r + i];

            if (rtok === endToken) return { j : l + i };
            if (ltok !== rtok) return false;
        }

        return false;
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
