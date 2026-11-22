import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.ProdGenMem
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.GoodAwayEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1368

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.GoodAwayEx
section
noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFock

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem fP_one_ne {m n : ℕ} (u : Fin m → Fin n → ℂ) : fP (1 : PX m n) u ≠ 0 := by
  unfold fP evX gs
  rw [map_one, one_mul]
  exact Complex.exp_ne_zero _

theorem goodAwayEx : GoodAwayEx := by
  intro F E _ _ _ _ _ σ d R w
  let g := (GlobalTheory.RealLift.intPts F (Fin d.m × Fin d.n × Fin 2)).indicator (1 : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ)
  have hg : g ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F) := GlobalTheory.RealLift.indicator_intPts_mem_SB
  let Ψ : Mx F E d.m d.n → ℂ := fun X =>
    (∏ w' ∈ Finset.univ.erase w, fP (1 : PX d.m d.n) (R.loc w' X)) * g fun k => (d.crd X k).2
  have hΨ : Ψ ∈ R.away w := Submodule.subset_span ⟨fun _ => 1, g, hg, rfl⟩
  refine ⟨Ψ, away_inv R w Ψ hΨ, fun h0 => ?_, fun f hf => tens_mem d R w f hf Ψ hΨ⟩
  have h1 := congrFun h0 0
  have hc : (fun k => (d.crd (0 : Mx F E d.m d.n) k).2) = 0 := by
    funext k
    unfold SD.crd
    rw [Matrix.zero_apply, map_zero, Finsupp.zero_apply]
    rfl
  have hg0 : g (fun k => (d.crd (0 : Mx F E d.m d.n) k).2) = 1 := by
    rw [hc]
    exact Set.indicator_of_mem GlobalTheory.RealLift.zero_mem_intPts _
  have hp : (∏ w' ∈ Finset.univ.erase w, fP (1 : PX d.m d.n) (R.loc w' 0)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun w' _ => fP_one_ne _
  exact hp (by simpa [Ψ, hg0] using h1)

end PositivityTheory.SiegelWeilFormula.KFock

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.LiftExOf
section
noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFock

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem fockMem : FockMem := by
  intro F E _ _ _ _ _ σ d R
  exact ⟨fock_le d R, fun w Ψ hΨ => ⟨fun P => away_tens R w Ψ hΨ P, away_inv R w Ψ hΨ⟩, fun w f hf => fock_dec R w f hf⟩

theorem T_sub (d : SD σ) (Φ Φ' : d.Fn) : d.T (Φ - Φ') = d.T Φ - d.T Φ' := by
  have h := T_add d (Φ - Φ') Φ'
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

theorem T_inj (hB : TBij) (d : SD σ) {Φ Φ' : d.Fn} (h : Φ ∈ d.sch) (h' : Φ' ∈ d.sch) (e : d.T Φ = d.T Φ') : Φ = Φ' :=
  sub_eq_zero.mp ((hB F E σ d).2.2 _ (d.sch.sub_mem h h') (by rw [T_sub, e, sub_self]))

theorem linLift (hB : TBij) (d : SD σ) {V : Type} [AddCommGroup V] [Module ℂ V] (t : V →ₗ[ℂ] (Mx F E d.m d.n → ℂ))
    (ht : ∀ v, t v ∈ d.schM) : ∃ φ : V →ₗ[ℂ] d.Fn, ∀ v, φ v ∈ d.sch ∧ d.T (φ v) = t v := by
  choose φ0 hφ0 using fun v => (hB F E σ d).2.1 (t v) (ht v)
  refine ⟨{ toFun := φ0, map_add' := fun v v' => ?_, map_smul' := fun a v => ?_ }, fun v => hφ0 v⟩
  · refine T_inj hB d (hφ0 (v + v')).1 (d.sch.add_mem (hφ0 v).1 (hφ0 v').1) ?_
    rw [T_add, (hφ0 _).2, (hφ0 _).2, (hφ0 _).2, map_add]
  · refine T_inj hB d (hφ0 (a • v)).1 (d.sch.smul_mem a (hφ0 v).1) ?_
    rw [RingHom.id_apply, T_smul, (hφ0 _).2, (hφ0 _).2, map_smul]

theorem fP_add {m n : ℕ} (P Q : PX m n) : fP (P + Q) = fP P + fP Q := by
  funext u
  simp only [fP, evX, map_add, Pi.add_apply, add_mul]

theorem fP_smul {m n : ℕ} (a : ℂ) (P : PX m n) : fP (a • P) = a • fP P := by
  funext u
  simp only [fP, evX, MvPolynomial.smul_eval, Pi.smul_apply, smul_eq_mul, mul_assoc]

def tensP {d : SD σ} (R : RD d) (w : InfinitePlace F) (Ψ : Mx F E d.m d.n → ℂ) : PX d.m d.n →ₗ[ℂ] (Mx F E d.m d.n → ℂ) where
  toFun P := R.tens w (fP P) Ψ
  map_add' P Q := by
    funext X
    simp only [RD.tens, fP_add, Pi.add_apply, add_mul]
  map_smul' a P := by
    funext X
    simp only [RD.tens, fP_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]

def tensS {d : SD σ} (R : RD d) (w : InfinitePlace F) (Ψ : Mx F E d.m d.n → ℂ) :
    𝓢(Fin d.m → Fin d.n → ℂ, ℂ) →ₗ[ℂ] (Mx F E d.m d.n → ℂ) where
  toFun S := R.tens w S Ψ
  map_add' S S' := by
    funext X
    simp only [RD.tens, SchwartzMap.add_apply, Pi.add_apply, add_mul]
  map_smul' a S := by
    funext X
    simp only [RD.tens, SchwartzMap.smul_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]

theorem liftEx_of : TBij → FockMem → LiftEx := by
  intro hB hF F E _ _ _ _ _ σ d R w Ψ hΨ
  obtain ⟨φ, hφ⟩ := linLift hB d (tensP R w Ψ) fun P => (hF F E σ d R).1 (((hF F E σ d R).2.1 w Ψ hΨ).1 P)
  exact ⟨φ, hφ⟩

theorem liftEx (hB : TBij) : LiftEx := liftEx_of hB fockMem

theorem liftSw (hB : TBij) (d : SD σ) (R : RD d) (w : InfinitePlace F) (Ψ : Mx F E d.m d.n → ℂ) (hΨ : Ψ ∈ R.away w) :
    ∃ φ : 𝓢(Fin d.m → Fin d.n → ℂ, ℂ) →ₗ[ℂ] d.Fn, ∀ S, φ S ∈ d.sch ∧ d.T (φ S) = R.tens w S Ψ :=
  linLift hB d (tensS R w Ψ) fun S => tens_mem d R w S ⟨S, rfl⟩ Ψ hΨ

theorem liftSw1 (hB : TBij) (d : SD σ) (R : RD d) (w : InfinitePlace F) (f : (Fin d.m → Fin d.n → ℂ) → ℂ) (hf : IsSw f)
    (Ψ : Mx F E d.m d.n → ℂ) (hΨ : Ψ ∈ R.away w) : ∃ Φ ∈ d.sch, d.T Φ = R.tens w f Ψ :=
  (hB F E σ d).2.1 _ (tens_mem d R w f hf Ψ hΨ)

end PositivityTheory.SiegelWeilFormula.KFock

end
end

