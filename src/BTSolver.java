import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.PriorityQueue;

public class BTSolver
{

	// =================================================================
	// Properties
	// =================================================================

	private ConstraintNetwork network;
	private SudokuBoard sudokuGrid;
	private Trail trail;

	private boolean hasSolution = false;

	public String varHeuristics;
	public String valHeuristics;
	public String cChecks;

	// =================================================================
	// Constructors
	// =================================================================

	public BTSolver ( SudokuBoard sboard, Trail trail, String val_sh, String var_sh, String cc )
	{
		this.network    = new ConstraintNetwork( sboard );
		this.sudokuGrid = sboard;
		this.trail      = trail;

		varHeuristics = var_sh;
		valHeuristics = val_sh;
		cChecks       = cc;
	}

	// =================================================================
	// Consistency Checks
	// =================================================================

	// Basic consistency check, no propagation done
	private boolean assignmentsCheck ( )
	{
		for ( Constraint c : network.getConstraints() )
			if ( ! c.isConsistent() )
				return false;

		return true;
	}

	// =================================================================
	// Arc Consistency
	// =================================================================
	public boolean arcConsistency ( )
    {
        List<Variable> toAssign = new ArrayList<Variable>();
        List<Constraint> RMC = network.getModifiedConstraints();
        for(int i = 0; i < RMC.size(); ++i)
        {
            List<Variable> LV = RMC.get(i).vars;
            for(int j = 0; j < LV.size(); ++j)
            {
                if(LV.get(j).isAssigned())
                {
                    List<Variable> Neighbors = network.getNeighborsOfVariable(LV.get(j));
                    int assignedValue = LV.get(j).getAssignment();
                    for(int k = 0; k < Neighbors.size(); ++k)
                    {
                        Domain D = Neighbors.get(k).getDomain();
                        if(D.contains(assignedValue))
                        {
                            if(D.size() == 1)
                                return false;
                            if(D.size() == 2)
                                toAssign.add(Neighbors.get(k));
                            trail.push(Neighbors.get(k));
                            Neighbors.get(k).removeValueFromDomain(assignedValue);
                        }
                    }
                }
            }
        }
        if(!toAssign.isEmpty())
        {
            for(int i = 0; i < toAssign.size(); ++i)
            {
                Domain D = toAssign.get(i).getDomain();
                ArrayList<Integer> assign = D.getValues();
                trail.push(toAssign.get(i));
                toAssign.get(i).assignValue(assign.get(0));
            }
            return arcConsistency();
        }
        return network.isConsistent();
    }


	/**
	 * Part 1 TODO: Implement the Forward Checking Heuristic
	 *
	 * This function will do both Constraint Propagation and check
	 * the consistency of the network
	 *
	 * (1) If a variable is assigned then eliminate that value from
	 *     the square's neighbors.
	 *
	 * Note: remember to trail.push variables before you change their domain
	 *
	 * Return: a pair of a HashMap and a Boolean. The map contains the pointers to all MODIFIED variables, mapped to their MODIFIED domain. 
	 *         The Boolean is true if assignment is consistent, false otherwise.
	 */
	public Map.Entry<HashMap<Variable,Domain>, Boolean> forwardChecking()
	{
        HashMap<Variable, Domain> modifiedVariables = new HashMap<>();

		for (Variable var : network.getVariables()) {
			if (var.isAssigned()) {
				int assignedValue = var.getAssignment();
				List<Variable> neighbors = network.getNeighborsOfVariable(var);

				for (Variable neighbor : neighbors) {

					Domain neighborDomain = neighbor.getDomain();
					if (neighborDomain.contains(assignedValue)) {
						//push onto trail before pruning
						trail.push(neighbor);

						//remove from domain
						neighbor.removeValueFromDomain(assignedValue);

                        modifiedVariables.put(neighbor, neighborDomain);

						//check if domain is now empty
						if (neighborDomain.isEmpty()) {
							return Pair.of(modifiedVariables, false);
						}
					}
				}
			}
		}

		//it is consistent
		return Pair.of(modifiedVariables, true);
	}

	/**
	 * Part 2 TODO: Implement both of Norvig's Heuristics
	 *
	 * This function will do both Constraint Propagation and check
	 * the consistency of the network
	 *
	 * (1) If a variable is assigned then eliminate that value from
	 *     the square's neighbors.
	 *
	 * (2) If a constraint has only one possible place for a value
	 *     then put the value there.
	 *
	 * Note: remember to trail.push variables before you change their domain
	 * Return: a pair of a map and a Boolean. The map contains the pointers to all variables that were assigned during the whole 
	 *         NorvigCheck propagation, and mapped to the values that they were assigned. 
	 *         The Boolean is true if assignment is consistent, false otherwise.
	 */
	public Map.Entry<HashMap<Variable,Integer>,Boolean> norvigCheck ( )
	{
		HashMap<Variable, Integer> assignedVariables = new HashMap<>();
		boolean isConsistent = true;

		for (Variable var : network.getVariables()) {
			if (var.isAssigned()) {
				int assignedValue = var.getAssignment();
				List<Variable> neighbors = network.getNeighborsOfVariable(var);

				for (Variable neighbor : neighbors) {
					if (!neighbor.isAssigned() && neighbor.getDomain().contains(assignedValue)) {
						trail.push(neighbor);
						neighbor.removeValueFromDomain(assignedValue);

						if (neighbor.getDomain().isEmpty()) {
							// inconsistent
							isConsistent = false;
							break;
						}
					}
				}

				if (!isConsistent) {
					break;
				}
			}
		}

		for (Constraint constraint : network.getConstraints()) {
			if (constraint.vars.size() == 1) {
				Variable var = constraint.vars.get(0);
				if (!var.isAssigned() && var.getDomain().size() == 1) {
					int assignedValue = -1;
					for (int value : var.getDomain()) {
						assignedValue = value;
					}
					// assign value to the var and push onto map
					var.assignValue(assignedValue);
					assignedVariables.put(var, assignedValue);
				}
			}
		}

		return Map.entry(assignedVariables, isConsistent);
	}

	/**
	 * Optional TODO: Implement your own advanced Constraint Propagation
	 *
	 * Completing the three tourn heuristic will automatically enter
	 * your program into a tournament.
	 */
	private boolean getTournCC ( )
	{
		return false;
	}

	// =================================================================
	// Variable Selectors
	// =================================================================

	// Basic variable selector, returns first unassigned variable
	private Variable getfirstUnassignedVariable()
	{
		for ( Variable v : network.getVariables() )
			if ( ! v.isAssigned() )
				return v;

		// Everything is assigned
		return null;
	}

	/**
	 * Part 1 TODO: Implement the Minimum Remaining Value Heuristic
	 *
	 * Return: The unassigned variable with the smallest domain
	 */
	public Variable getMRV ( )
	{
		Variable mrvVar = null;
		int mrv = Integer.MAX_VALUE;

		//iterate through all unassigned variables
		for (Variable var : network.getVariables()) {
			if (!var.isAssigned()) {
				int domainSize = var.getDomain().size();
				//take the smallest domain size
				if (domainSize < mrv) {
					mrv = domainSize;
					mrvVar = var;
				}
			}
		}

		return mrvVar;
	}

	/**
	 * Part 2 TODO: Implement the Minimum Remaining Value Heuristic
	 *                with Degree Heuristic as a Tie Breaker
	 *
	 * Return: The unassigned variable with the smallest domain and affecting the most unassigned neighbors.
	 *         If there are multiple variables that have the same smallest domain with the same number 
	 *         of unassigned neighbors, add them to the list of Variables.
	 *         If there is only one variable, return the list of size 1 containing that variable.
	 */

	public List<Variable> MRVwithTieBreaker() {
		//pq with comparator by domain sizes (lower domain = higher prio)
		PriorityQueue<Variable> minVarsQueue = new PriorityQueue<>(Comparator.comparingInt(var -> var.getDomain().size()));
		List<Variable> minVars = new ArrayList<>();

		// load all unassigned vars into pq
		for (Variable var : network.getVariables()) {
			if (!var.isAssigned()) {
				minVarsQueue.add(var);
			}
		}

		// need to add null to list because the program expects at least 1 val
		if (minVarsQueue.isEmpty()) {
			minVars.add(null);
			return minVars;
		}

		// we extract all the variables having the min. value
		Variable prevMinVar = null;
		while (!minVarsQueue.isEmpty()) {
			Variable var = minVarsQueue.poll();

			// stop extracting if domain size increases
			if (prevMinVar != null && var.getDomain().size() != prevMinVar.getDomain().size()) {
				break;
			}
			minVars.add(var);
			prevMinVar = var;
		}

		return minVars;
	}


	/**
	 * Optional TODO: Implement your own advanced Variable Heuristic
	 *
	 * Completing the three tourn heuristic will automatically enter
	 * your program into a tournament.
	 */
	private Variable getTournVar ( )
	{
		return null;
	}

	// =================================================================
	// Value Selectors
	// =================================================================

	// Default Value Ordering
	public List<Integer> getValuesInOrder ( Variable v )
	{
		List<Integer> values = v.getDomain().getValues();

		Comparator<Integer> valueComparator = new Comparator<Integer>(){

			@Override
			public int compare(Integer i1, Integer i2) {
				return i1.compareTo(i2);
			}
		};
		Collections.sort(values, valueComparator);
		return values;
	}

	/**
	 * Part 1 TODO: Implement the Least Constraining Value Heuristic
	 *
	 * The Least constraining value is the one that will knock the least
	 * values out of it's neighbors domain.
	 *
	 * Return: A list of v's domain sorted by the LCV heuristic
	 *         The LCV is first and the MCV is last
	 */
	public List<Integer> getValuesLCVOrder ( Variable v )
	{
		//find the value for var that will take out the least remaining values from neighbors domain
		//we can avoid reassigning and backtracking more this way (hopefully)
		Domain domain = v.getDomain();
		//key = var's val, val = the num to be removed from neighbor's domain
		Map<Integer, Integer> valueCountMap = new HashMap<>();

		// Iterate over each value in the variable's domain
		for(int value : domain.getValues()) {
			int count = 0;

			for(Variable neighbor : network.getNeighborsOfVariable(v)) {
				//check if neighbor has that value in domain that will need to be removed
				if(neighbor.getDomain().contains(value)) {
					count++;
				}
			}
			valueCountMap.put(value, count);
		}

		//sort by count value asc
		List<Integer> sortedValues = new ArrayList<>(domain.getValues());
		sortedValues.sort(Comparator.comparingInt(valueCountMap::get));

		// Return the sorted list of values
		return sortedValues;
	}

	/**
	 * Optional TODO: Implement your own advanced Value Heuristic
	 *
	 * Completing the three tourn heuristic will automatically enter
	 * your program into a tournament.
	 */
	public List<Integer> getTournVal ( Variable v )
	{
		return null;
	}

	//==================================================================
	// Engine Functions
	//==================================================================

	public int solve (float time_left)
	{
		if(time_left <= 60.0) {
			return -1;
		}
		long startTime = System.nanoTime();
		if ( hasSolution )
			return 0;

		// Variable Selection
		Variable v = selectNextVariable();

		if ( v == null )
		{
			for ( Variable var : network.getVariables() )
			{
				// If all variables haven't been assigned
				if ( ! var.isAssigned() )
				{
					return 0;
				}
			}

			// Success
			hasSolution = true;
			return 0;
		}

		// Attempt to assign a value
		for ( Integer i : getNextValues( v ) )
		{
			// Store place in trail and push variable's state on trail
			trail.placeTrailMarker();
			trail.push( v );

			// Assign the value
			v.assignValue( i );

			// Propagate constraints, check consistency, recurse
			if ( checkConsistency() ) {
				long endTime = System.nanoTime();
                long elapsedTime = (endTime - startTime);
                float elapsedSecs = ((float)(endTime - startTime)) / 1000000000;
                float new_start_time = time_left - elapsedSecs;
				int check_status = solve(new_start_time);
				if(check_status == -1) {
				    return -1;
				}
			}

			// If this assignment succeeded, return
			if ( hasSolution )
				return 0;

			// Otherwise backtrack
			trail.undo();
		}
		return 0;
	}

	public boolean checkConsistency ( )
	{
		switch ( cChecks )
		{
			case "forwardChecking":
				return forwardChecking().getValue();

			case "norvigCheck":
				return norvigCheck().getValue();

			case "tournCC":
				return getTournCC();

			default:
				return assignmentsCheck();
		}
	}

	public Variable selectNextVariable ( )
	{
		switch ( varHeuristics )
		{
			case "MinimumRemainingValue":
				return getMRV();

			case "MRVwithTieBreaker":
				return MRVwithTieBreaker().get(0);

			case "tournVar":
				return getTournVar();

			default:
				return getfirstUnassignedVariable();
		}
	}

	public List<Integer> getNextValues ( Variable v )
	{
		switch ( valHeuristics )
		{
			case "LeastConstrainingValue":
				return getValuesLCVOrder( v );

			case "tournVal":
				return getTournVal( v );

			default:
				return getValuesInOrder( v );
		}
	}

	public boolean hasSolution ( )
	{
		return hasSolution;
	}

	public SudokuBoard getSolution ( )
	{
		return network.toSudokuBoard ( sudokuGrid.getP(), sudokuGrid.getQ() );
	}

	public ConstraintNetwork getNetwork ( )
	{
		return network;
	}
}
