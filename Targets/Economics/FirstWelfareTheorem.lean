import Applied.Economics.Welfare

/-!
# First fundamental theorem of welfare economics

- id: econ-first-welfare-theorem
- area: economics
- status: formalized
- source: K. J. Arrow, "An extension of the basic theorems of classical welfare economics" (1951); G. Debreu, "Theory of Value" (1959); textbook form: Mas-Colell, Whinston, Green, "Microeconomic Theory" (1995), Proposition 16.C.1
- used-in: the efficiency case for competitive markets; a baseline in market design and policy analysis
- prerequisites: inner product spaces
- statement-review: unreviewed

Informal statement. In an exchange economy where every agent's preferences are locally
non-satiated, a competitive equilibrium allocation is Pareto efficient: no feasible allocation
makes everyone at least as well off and someone strictly better off.

Scope: pure exchange, consumption sets equal to the whole commodity space, finitely many
agents. Not yet covered: production, restricted consumption sets, the second welfare theorem.
-/

namespace Targets.Economics

alias first_welfare_theorem := Applied.Economics.competitive_equilibrium_pareto_efficient

end Targets.Economics
