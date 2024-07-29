
try {
    
    let guidZ = 0n;
    let tokenLibraryMap = new Map ();
    let tokenLibraryInverseMap = new Map ();
    const PrimeNumberArray = [
        3n, 5n, 7n, 11n, 13n, 17n, 19n, 23n, 29n, 31n, 37n, 41n, 43n, 47n, 53n, 59n, 61n, 67n, 71n, 
        73n, 79n, 83n, 89n, 97n, 101n, 103n, 107n, 109n, 113n, 127n, 131n, 137n, 139n, 149n, 151n, 157n, 
        163n, 167n, 173n, 179n, 181n, 191n, 193n, 197n, 199n, 211n, 223n, 227n, 229n, 233n, 239n, 241n, 
        251n, 257n, 263n, 269n, 271n, 277n, 281n, 283n, 293n, 307n, 311n, 313n, 317n, 331n, 337n, 347n, 
        349n, 353n, 359n, 367n, 373n, 379n, 383n, 389n, 397n, 401n, 409n, 419n, 421n, 431n, 433n, 439n, 
        443n, 449n, 457n, 461n, 463n, 467n, 479n, 487n, 491n, 499n, 503n, 509n, 521n, 523n, 541n, 547n, 
        557n, 563n, 569n, 571n, 577n, 587n, 593n, 599n, 601n, 607n, 613n, 617n, 619n, 631n, 641n, 643n, 
        647n, 653n, 659n, 661n, 673n, 677n, 683n, 691n, 701n, 709n, 719n, 727n, 733n, 739n, 743n, 751n, 
        757n, 761n, 769n, 773n, 787n, 797n, 809n, 811n, 821n, 823n, 827n, 829n, 839n, 853n, 857n, 859n, 
        863n, 877n, 881n, 883n, 887n, 907n, 911n, 919n, 929n, 937n, 941n, 947n, 953n, 967n, 971n, 977n, 
        983n, 991n, 997n, 1009n, 1013n, 1019n, 1021n, 1031n, 1033n, 1039n, 1049n, 1051n, 1061n, 1063n, 
        1069n, 1087n, 1091n, 1093n, 1097n, 1103n, 1109n, 1117n, 1123n, 1129n, 1151n, 1153n, 1163n, 1171n, 
        1181n, 1187n, 1193n, 1201n, 1213n, 1217n, 1223n, 1229n, 1231n, 1237n, 1249n, 1259n, 1277n, 1279n, 
        1283n, 1289n, 1291n, 1297n, 1301n, 1303n, 1307n, 1319n, 1321n, 1327n, 1361n, 1367n, 1373n, 1381n, 
        1399n, 1409n, 1423n, 1427n, 1429n, 1433n, 1439n, 1447n, 1451n, 1453n, 1459n, 1471n, 1481n, 1483n, 
        1487n, 1489n, 1493n, 1499n, 1511n, 1523n, 1531n, 1543n, 1549n, 1553n, 1559n, 1567n, 1571n, 1579n, 
        1583n, 1597n, 1601n, 1607n, 1609n, 1613n, 1619n, 1621n ];

    function solveProblem () {
        const {axioms, proofStatement} = parseInput (document.getElementById ('input').value);
        const startTime = performance.now ();
        document.getElementById ('output').value = generateProof (axioms, proofStatement);
        output.value += `\n\nTotal runtime: ${performance.now () - startTime} Milliseconds`;
    } // end solveProblem

    function parseInput (input) {
        let pKeyZ;
        const lines = input.split ('\n').filter (line => line.trim () && !line.startsWith ('//'));
        return {
            axioms: lines
                .slice (0, -1)
                    .map ((line,idx,me) => line
                        .split (/[~<]?=+[>]?/g)
                            .sort ((a,b) => a.length <= b.length )
                                .map ((tokens,idx,me) => { tokens = tokens
                                    .trim ()
                                        .split (/\s+/)
                                            .map ((u,thisIdx,thisArray) => {
                                                (thisIdx < 1) && (pKeyZ = 1n);
                                                pKeyZ = updateTokenZValues(u, pKeyZ);
                                                return u;
                                            });
                                            return { tokens, pKeyZ };
                                        })),
            proofStatement: lines [lines.length - 1]
        };
    } // end parseInput

    function generateProof (axioms, proofStatement) {
        let pKeyZ;
        let [lhs, rhs] = proofStatement
            .split (/[~<]?=+[>]?/g)
                .map ((tokens,idx,me) => {
                    tokens = tokens.trim ()
                        .split (/\s+/)
                            .map ((u,thisIdx,thisArray) => {
                                (thisIdx < 1) && (pKeyZ = 1n);
                                pKeyZ = updateTokenZValues(u, pKeyZ);
                                return u;
                            });
                        return { tokens, pKeyZ };
                    });
        let steps = [];

        const applyRules = (sides, action) => {
            sides = sides.map ((current,idx,me) => {
                let changed;
                const other = idx == 0 ? me [1] : me [0] ;
                const side = idx == 0 ? 'lhs' : 'rhs' ;
                do {
                    changed = applyRule (current, axioms, action);
                    if (changed) {
                        steps.push ({ side, action, result: structuredClone(changed.result), axiom: changed.axiom, other: structuredClone(other) });
                        current = changed.result;
                    }
                } while (changed && current.tokens.join (' ') !== other.tokens.join (' '));
                return current;
            });
            return (sides [0].tokens.join (' ') == sides [1].tokens.join (' '));
        };

        const proofFound = (() => {
            let ret = applyRules ([structuredClone(lhs), structuredClone(rhs)],'reduce');
            ret == (lhs.tokens.join (' ') == rhs.tokens.join (' '));
            !ret && (steps = []) && (ret = applyRules ([structuredClone(lhs), structuredClone(rhs)], 'expand'));
            return ret;
        })();

        return `${proofFound ? 'Proof' : 'Partial-proof'} found!\n\n${proofStatement}, (root)\n` +
            steps.map (step => `${step.side === 'lhs' ? step.result.tokens.join (' ') : step.other.tokens.join (' ')} = ${step.side === 'lhs' ? step.other.tokens.join (' ') : step.result.tokens.join (' ')}, (${step.side} ${step.action}) via ${step.axiom}`).join ('\n') +
            (proofFound ? '\n\nQ.E.D.' : '');
    } // end generateProof

    function applyRule (expression, axioms, action) {
        for (let i = 0; i < axioms.length; i++) {
            const [left, right] = axioms [i];
            const match = action === 'reduce' ? left : right;
            const replacer = action === 'reduce' ? right : left;
            if (expression._includes (match)) {
                return {
                    result: expression._replace (match, replacer),
                    axiom: `axiom_${i + 1}.0`,
                };
            }
        }
        return null;
    } // end applyRule

    function updateTokenZValues(u,pKeyZ) {
        if (!((guidZ+1n) in PrimeNumberArray))
            PrimeNumberArray.push (nextPrime ());
        if (!tokenLibraryMap.has (u)) {
            const primeZ = PrimeNumberArray[guidZ++];
            tokenLibraryMap.set (u, primeZ);
            tokenLibraryInverseMap.set (primeZ, u);
        }
        const tokZ = tokenLibraryMap.get(u);
        pKeyZ *= tokZ;
        return pKeyZ;
    } // end updateTokenZValues

    Object.prototype._includes = function (indir) {
        let ret = false;
        const self = this;
        if ((self.pKeyZ >= indir.pKeyZ) 
            && (self._containsPrimaryKey(indir.pKeyZ))
                && (self.tokens.length >= indir.tokens.length)){
            let i = 0;
            let _self = self.tokens;
            const _tokens = indir.tokens;
            for (let tok of _self) {
                if (_tokens [i] === tok)
                    ++i;
                !ret && (ret = (_tokens.length == i));
                if (ret)
                    break;
            }
        }
        return ret;
    } // end Object.prototype._includes

    Object.prototype._containsPrimaryKey = function  (indirKeyZ) {
        const exprKeyz = this.pKeyZ;
        const statusFlag = exprKeyz % indirKeyZ == 0n;
        return statusFlag;
    }

    Object.prototype._replace = function (from, to) {
        let ret = false;
        let self = structuredClone(this);
        const _from = from.tokens;
        const _to = to.tokens;
        let _self = self.tokens;
        if (_self.length >= _from.length){
            let i = 0;
            let j = 0;
            let tokenIDX = [];
            for (let tok of _self) {
                if (_from [i] === tok){
                    tokenIDX.push (j);
                    ++i;
                }
                !ret && (ret = (_from.length == i));
                if (ret){
                    tokenIDX.forEach ((k,idx,me) => {
                        _self [k] = '';
                    });
                    _self [j] = _to.join (' ');
                    self.pKeyZ = updatePrimaryKey(self.pKeyZ,from.pKeyZ,to.pKeyZ);
                    i = 0;
                    ret = false;
                    tokenIDX = [];
                }
                ++j;
            }
        }
        self.tokens = _self
            .join (' ')
                .split (/\s+/)
                    .filter (u => u)
                        .map ((s,index,me) => s
                            .trim ());
        return self;
    } // end Object.prototype._replace

    function updatePrimaryKey (pKeyZ,fromKeyZ,toKeyZ) {
        pKeyZ = pKeyZ / fromKeyZ * toKeyZ;
        return pKeyZ;
    }

    function isPrime (num) {
        if (num <= 1n) return false;
        if (num <= 3n) return true;

        // Check divisibility from 2 to the square root of num
        for (let i = 2n; i * i <= num; ++i) {
            if (num % i == 0) return false;
        }
        return true;
    }; // end isPrime

    function nextPrime () {
        var num = LASTPRIMEIDX;
        while (1n) {
            if (isPrime (num)) {
                LASTPRIMEIDX = num + 2n;
                return num;
            }
            num += 2n; // only check odd numbers //
        }
    }; // end nextPrime

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