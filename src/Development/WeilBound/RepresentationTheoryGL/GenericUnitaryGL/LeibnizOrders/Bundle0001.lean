import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet

-- bundled from Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.DerLSeg
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib

namespace GlobalTheory.RgGu.Leib

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def DerLSeg : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (Δ : Segment k) (N : ℕ) (π : GRep k N), IsSmooth π.ρ → IsLSeg Δ π.ρ →
      ∀ (m n : ℕ) (hm : N = n + m),
        (¬ Δ.d ∣ m → Subsingleton (derivB ψ m (π.cast hm)).V) ∧
        (∀ (a : ℕ) (ha : a < Δ.len), m = a * Δ.d →
          IsLSeg (Zc.segHigh Δ a ha) ((derivB ψ m (π.cast hm)).tw (-(m : ℝ) / 2)).ρ) ∧
        (m = Δ.len * Δ.d → Module.rank ℂ (derivB ψ m (π.cast hm)).V = 1)

end GlobalTheory.RgGu.Leib

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.PhiPG0
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib

namespace GlobalTheory.RgGu.Leib

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def PhiPG0 : Prop :=
  ∀ (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (t : ℕ) (τ : MRep k 0) (σ : GRep k (t + 1)), IsSmooth σ.ρ →
      MIso (phiN ψ (mcast (by omega : 0 + (t + 1) = (0 + t) + 1) (prodPGn τ σ))) (prodGPn (psiN τ) (gres σ))

end GlobalTheory.RgGu.Leib

end
end

