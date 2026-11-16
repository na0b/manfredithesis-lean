/- Run with `lake env lean Axioms.lean` after `lake build`.
Every result below should depend only on `propext`, `Classical.choice` and `Quot.sound`. -/
import ManfrediThesis

#print axioms DeGiorgiSequenceLemma
#print axioms DeGiorgiLevelSetMeasure
#print axioms LevelTruncationMaximumPrinciple
#print axioms LevelSetMeasureImprovement
#print axioms OscillationDecayLemma
#print axioms DirichletProblemRestricted
#print axioms GradientSupEstimate
#print axioms GradientOscillationEstimate
#print axioms DegenerateAlternative
#print axioms ComparisonGradientEstimateMin
#print axioms MorreyGradientToCampanato
#print axioms CampanatoIterationLemma
#print axioms MinimumMorreyRegularity
#print axioms MinimumGradientHolder
#print axioms ComparisonGradientEstimateGeneral
#print axioms SolutionMorreyRegularity
#print axioms SolutionGradientHolder
#print axioms QuasiregularRegularity
