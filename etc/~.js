
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
