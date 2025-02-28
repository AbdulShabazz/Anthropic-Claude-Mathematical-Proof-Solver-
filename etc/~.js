
            /*
            let wVal;
            let xVal;
            let yVal;
            let zVal;
            */
            /*
            const ww = reduceLHS(axioms);
            const xx = reduceRHS(axioms);
            const yy = expandLHS(axioms);
            const zz = expandRHS(axioms);
            */
                /*
                wVal = ww?.next()?.value;
                xVal = xx?.next()?.value;
                yVal = yy?.next()?.value;
                zVal = zz?.next()?.value;
                */


const w = reduceLHS(axioms);
const x = reduceRHS(axioms);
const y = expandLHS(axioms);
const z = expandRHS(axioms);

function* reduceLHS(_axioms_) {
    while (1) {
        if (proofFoundFlag || reduce_lhs_queue.length < 1)
            return 0;
        const _lhs_ = reduce_lhs_queue.shift();
        for (let axiom of _axioms_) {
            let tmp = [..._lhs_];
            const curr_rewrite = `${_lhs_.join(' ')}`;
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
            } // end if (rewriteFoundFlag)
        } // end for (let axiom of _axioms)
    } // end while (1)
} // end reduceLHS

function* reduceRHS(_axioms_) {
    while (1) {
        if (proofFoundFlag || reduce_rhs_queue.length < 1)
            return 0;
        const _rhs_ = reduce_rhs_queue.shift();
        for (let axiom of _axioms_) {
            let tmp = [..._rhs_];
            const curr_rewrite = `${_rhs_.join(' ')}`;
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
            } // end if (rewriteFoundFlag)
        } // end for (let axiom of _axioms)
    } // end while (1)
} // end reduceRHS

function* expandLHS(_axioms_) {
    while (1) {
        if (proofFoundFlag || expand_lhs_queue.length < 1)
            return 0;
        const _lhs_ = expand_lhs_queue.shift();
        for (let axiom of _axioms_) {
            let tmp = [..._lhs_];
            const curr_rewrite = `${_lhs_.join(' ')}`;
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
            } // end if (rewriteFoundFlag)
        } // end for (let axiom of _axioms)
    } // end while (1)
} // end expandLHS

function* expandRHS(_axioms_) {
    while (1) {
        if (proofFoundFlag || expand_rhs_queue.length < 1)
            return 0;
        const _rhs_ = expand_rhs_queue.shift();
        for (let axiom of _axioms_) {
            let tmp = [..._rhs_];
            const curr_rewrite = `${_rhs_.join(' ')}`;
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
            } // end if (rewriteFoundFlag)
        } // end for (let axiom of _axioms)
    } // end whiile (1)
} // end expandRHS
                    /*
                    let rewriteFoundFlag_reduce_lhs;
                    let rewriteFoundFlag_reduce_rhs;
                    let rewriteFoundFlag_expand_lhs;
                    let rewriteFoundFlag_expand_rhs;
                    */

                    
                        /*
                        rewriteFoundFlag_reduce_rhs = false;
                        rewriteFoundFlag_expand_lhs = false;
                        rewriteFoundFlag_expand_rhs = false;
                        */
let steps = [];

        //let proofsteps = [];

        ///buildAllSubnetCallGraphsF (sortedAxioms);

    //let LHS_commit_history = new Set();
    //let RHS_commit_history = new Set();

function buildAllSubnetCallGraphsF (unsortedAxiomsArray) {
    const I = unsortedAxiomsArray.length;
    const J = unsortedAxiomsArray.length - 1; // disallow root

    for (let i = 0; i < I; i++) {
        let axiom_00 = unsortedAxiomsArray [i];
        for (let j = 0; j < J; j++) {
            if (i == j) continue ;
            let axiom_01 = unsortedAxiomsArray [j];
            let [ axiom_01_lhs, axiom_01_rhs ] = axiom_01.subnets;
            buildSubnetCallGraphF (axiom_00, j, axiom_01_lhs, 'lhs');
            buildSubnetCallGraphF (axiom_00, j, axiom_01_rhs, 'rhs');
        } // end for (let j = 0; j < J; j++)
    } // end for (let i = 0; i < I; i++)

} // end buildSubnetCallGraphs (...)

function buildSubnetCallGraphF (axiom, i, from, indirectionSZ) {
    let [ lhs, rhs ] = axiom.subnets;
    const ci_lhsZ = lhs._tryReplace (from, [true]);
    const ci_rhsZ = rhs._tryReplace (from, [true]);
    const subnetReduceFlag = Boolean(/^lhs/.test(indirectionSZ)); // reduce: lhs => rhs
    if (ci_lhsZ && subnetReduceFlag) {
        AddToLHSReduce (axiom, i);
    } else if (ci_lhsZ) {
        AddToLHSExpand (axiom, i);
    }
    if (ci_rhsZ && subnetReduceFlag) {
        AddToRHSReduce (axiom, i);
    } else if (ci_rhsZ) {
        AddToRHSExpand (axiom, i);
    }
} // end buildSubnetCallGraphF (axiom, from, to)

function AddToLHSReduce (axiom, i) {
    (axiom._lhsReduce == undefined) && (axiom._lhsReduce = []);
    axiom._lhsReduce.push (i);
} // end AddToLHSReduce

function AddToLHSExpand (axiom, i) {
    (axiom._lhsExpand == undefined) && (axiom._lhsExpand = []);
    axiom._lhsExpand.push (i);
} // end AddToLHSExpand

function AddToRHSReduce (axiom, i) {
    (axiom._rhsReduce == undefined) && (axiom._rhsReduce = []);
    axiom._rhsReduce.push (i);
} // end AddToRHSReduce

function AddToRHSExpand (axiom, i) {
    (axiom._rhsExpand == undefined) && (axiom._rhsExpand = []);
    axiom._rhsExpand.push (i);
} // end AddToRHSExpand

function applyRule (guidZ, expression, tmpAxioms, action) {
    const axiomIDS = (() => {
        let tmpA = [];
        switch (action) {
            case 'reduce':
                if (tmpAxioms [guidZ]?._lhsReduce) {
                    tmpA.push (
                        ...tmpAxioms [guidZ]?._lhsReduce
                    );
                }
                if (tmpAxioms [guidZ]?._rhsReduce) {
                    tmpA.push (
                        ...tmpAxioms [guidZ]?._rhsReduce
                    );
                }
                break;
            case 'expand':
                if (tmpAxioms [guidZ]?._lhsExpand) {
                    tmpA.push (
                        ...tmpAxioms [guidZ]?._lhsExpand
                    );
                }
                if (tmpAxioms [guidZ]?._rhsExpand) {
                    tmpA.push (
                        ...tmpAxioms [guidZ]?._rhsExpand
                    );
                }
                break;
        } // end switch (action)
        return tmpA;
    }) ();
    let batchRewrites = [];
    const I = axiomIDS.length;
    for (let i = 0; i < I; i++) {
        const uuid = axiomIDS [i];
        if (uuid == guidZ)
            continue;
        const axiom = tmpAxioms [uuid];
        const [left, right] = axiom.subnets;
        const from = action === 'reduce' ? left : right;
        const to = action === 'reduce' ? right : left;
        const rewriteFound = expression._tryReplace (from, to);
        if (rewriteFound) {
            batchRewrites.push( {
                result: rewriteFound,
                axiomID: axiom.axiomID,
                axiomRewriteID: uuid,
            });
        }
    } // end for (let i = 0; i < I; i++)
    return batchRewrites;
} // end applyRule

/*
        !proofFound
            && (result = proofsteps
                .sort((a,b) => b.length > a.length)
                    .shift());

        return `${proofFound ? 'Proof' : 'Partial-proof'} found!\n\n${proofStatement.subnets [0].join (' ')} = ${proofStatement.subnets [1].join (' ')}, (root)\n`
            + steps
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
                .join ('\n')
                    + (proofFound ? '\n\nQ.E.D.' : '');
        */
                    function _applyAxioms (tmpAxioms, guidZ, sides, action) {
                        sides = sides.map ((current,idx,me) => {
                            let lastGUIDZ = guidZ;
                            let changed;
                            const side = idx == 0 ? 'lhs' : 'rhs' ;
                            do {
                                changed = applyRule (lastGUIDZ, current, tmpAxioms, action);
                                for (let ch of changed) {
                                    steps.push ({ side, action, result: [...ch.result], axiomID: ch.axiomID, other: [] });
                                    current = ch.result;
                                    lastGUIDZ = ch.axiomRewriteID;
                                }
                            } while (changed?.length > 0);
                            return current;
                        });
                        return (sides [0].join (' ') == sides [1].join (' '));
                    } // end applyAxioms
            
                    function applyAxioms (tmpAxioms, guidZ, sides, action) {
                        /*
                        sides = sides.map ((current,idx,me) => {
                            let lastGUIDZ = guidZ;
                            let changed;
                            const side = idx == 0 ? 'lhs' : 'rhs' ;
                            do {
                                changed = applyRule (lastGUIDZ, current, tmpAxioms, action);
                                for (let ch of changed) {
                                    steps.push ({ side, action, result: [...ch.result], axiomID: ch.axiomID, other: [] });
                                    current = ch.result;
                                    lastGUIDZ = ch.axiomRewriteID;
                                }
                            } while (changed?.length > 0);
                            return current;
                        });
                        return (sides [0].join (' ') == sides [1].join (' '));
                        */
                    } // end applyAxioms

/*
            if (lhs.join (' ') == rhs.join (' '))
                return true;
            let ret = applyAxioms (axioms, proofStatement.guidZ, [[...lhs], [...rhs]],'reduce');
            ret == (lhs.join (' ') == rhs.join (' '));
            // reduce failed? Try expand!
            !ret
                && (proofsteps.push ([...steps]))
                    && (steps = [])
                        && (ret = applyAxioms (axioms, proofStatement.guidZ, [[...lhs], [...rhs]], 'expand'));
            proofsteps.push ([...steps]);
            return ret;
            */

    /**************************************************
     * Term-Rewriting System with Generator Function
     **************************************************/
    function* rewriteGenerator(theorem, theorem_to_prove, axioms) {
        // Track strings that we have seen already
        const visited = new Set();
        // Initialize our queue with the starting theorem
        const queue = [theorem];

        // Mark the starting theorem as visited
        visited.add(theorem);

        while (queue.length > 0) {
            // Take the next item from the queue
            const current = queue.shift();

            // Yield the current rewrite step
            yield current;

            // Check if we have reached our desired theorem
            if (current == theorem_to_prove) {
                // Stop the generator once the target is found
                return;
            }

            // Attempt all possible rewrites by applying every axiom
            for (const axiom of axioms) {
                for (const from in axiom) {
                    const to = axiom[from];

                    // Identify the placeholder pattern in the theorem text, e.g. {a} -> {b}
                    const matchPattern = `{${from}}`;
                    const rewritePattern = `{${to}}`;

                    // For each place that "from" occurs, replace and produce a new candidate
                    let startIndex = 0;
                    while (true) {
                        const idx = current.indexOf(matchPattern, startIndex);
                        if (idx === -1) {
                            break;
                        }
                        // Construct the new theorem string after rewriting
                        const newTheorem =
                            current.slice(0, idx)
                                + rewritePattern
                                    + current.slice(idx + matchPattern.length);

                        // If we have not seen this new rewrite, enqueue it for further exploration
                        if (!visited.has(newTheorem)) {
                            visited.add(newTheorem);
                            queue.push(newTheorem);
                        }

                        // Move past this occurrence to look for another
                        startIndex = idx + matchPattern.length;
                    }
                }
            }
        }
    } // rewriteGenerator(theorem, theorem_to_prove, axioms)

    /*

    // Example usage:

    // Define your axioms: each object means '{key}' -> '{value}'
    const axioms = [
        { 'a': 'b' },
        { '0': '1' },
        { 'y': 'z' }
    ];

    // Starting theorem
    const theorem = '{a} + {0} + {y}';
    // Target theorem we wish to prove
    const theorem_to_prove = '{b} + {1} + {z}';

    // Instantiate the generator
    const generator = rewriteGenerator(theorem, theorem_to_prove, axioms);

    // Collect the steps in an array for inspection
    const proofSteps = [];
    for (const step of generator) {
        console.log('Rewrite step:', step);
        proofSteps.push(step);

        if (step === theorem_to_prove) {
            break;
        }
    }

    console.log(proofSteps,'\n\n');

    if(proofSteps[proofSteps.length-1] == theorem_to_prove) {
        console.log('Q.E.D.');
    } else if (proofSteps.length > 0) {
        console.log('Partial-proof found.');
    } else {
        // If we never encountered the theorem_to_prove, no successful proof was found
        console.log('No proof found.');
    }

    */

class currentCommitCl {
    constructor(
      axiomIDW = '',
      flagPropertyNameW = '',   // e.g. 'alreadyReducedFlag' or 'alreadyExpandedFlag'
      flagValueBool = false,
      commitHistoryarray = []
    ) {
      // Create a sub-object that looks like: [axiomID]: { [flagPropertyName]: flagValue }
      this[axiomIDW] = {
        [flagPropertyNameW]: flagValueBool
      };

      // Attach commitHistory array
      this.commitHistoryarray = commitHistoryarray;
    }
}

    /**
     * example
     * '{ { { { a } + { b } + { c } }'
     *      .match(/\S+/g)
     *          .simplifyBraces ();
     * 
     * output
     *  [ "{", "a", "+", "b", "+", "c", "}" ]
     */
    Object.prototype.simplifyBraces = function() {
        let result = this;
        let lbrace = [];
        let rbrace = [];
        let pair = [];
        let deleteZ = new Map();
        const I = result.length;
        const lastIDXZ = I-1;
    
        // First pass: mark braces to remove
        for (let i = 0; i < I; i++) {
            if (result[i] === '{') {
                lbrace.push(i);
            } else if (result[i] === '}') {                
                rbrace.push(i);
            }
            if (lbrace.length > 0 && rbrace.length > 0) 
                pair.push(lbrace.pop(), rbrace.pop());
            if (pair.length > 1){
                const scopeExists = 
                    ((pair[1] - pair[0]) > 2) 
                        && !((pair [0] == 0) && (pair[1] == lastIDXZ));
                if (!scopeExists){
                    deleteZ.set (pair[0], true);
                    deleteZ.set (pair[1], true);
                }
                pair = [];
            }
            if (i == lastIDXZ) {
                // Mark any unmatched opening braces for deletion
                lbrace.forEach(index => deleteZ.set(index, true));      
        
                // Mark any unmatched closing braces for deletion
                rbrace.forEach(index => deleteZ.set(index, true));
            }
        } 

        // Second pass: remove marked braces and any trailing unclosed braces
        return result.filter((tok, i) => !deleteZ.has(i));
    } // end simplifyBraces
