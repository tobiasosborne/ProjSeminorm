import Mathlib.Analysis.Normed.Module.PiTensorProduct.InjectiveSeminorm
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.LinearAlgebra.PiTensorProduct.Dual
import Mathlib.Topology.Algebra.InfiniteSum.Order

open scoped TensorProduct BigOperators

namespace ProjSeminorm

universe uι u𝕜 uE

variable {ι : Type uι} [Fintype ι]
variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : ι → Type uE} [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

end ProjSeminorm
