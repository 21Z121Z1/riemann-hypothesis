import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0450
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.UnipotentAdelicQuotients.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0016
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedTopLevelChain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0454
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0452
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0311
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0445
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0158

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalBasisChangeIntegralUnitDet
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IntegralityCompare

noncomputable section

namespace GlobalTheory.LocBasisChange

theorem norm_le_one_of_isIntegral_int {C : Type} [NormedField C] [IsUltrametricDist C] {x : C}
    (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem norm_det_le_one {C : Type} [NormedField C] [IsUltrametricDist C] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) C) (h : ∀ a b, ‖M a b‖ ≤ 1) : ‖M.det‖ ≤ 1 := by
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  have hp : ‖∏ i, M (σ i) i‖ ≤ 1 := by
    rw [norm_prod]; exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => h _ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs]
  · rwa [one_smul]
  · rwa [Units.neg_smul, one_smul, norm_neg]

theorem norm_natCast_of_not_dvd {p : ℕ} [Fact p.Prime] {s : ℕ} (hs : ¬ p ∣ s) : ‖(s : ℂ_[p])‖ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hs

theorem basis_change : ∀ (D : D7) {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (Bm : GL (Fin N) D.host.E) (Bs : Matrix (Fin N) (Fin N) ℂ_[p]),
    GL3Columns.BasR D lam τ L Bs → Formalism.L2.Forms.IsLocBasis p (L : Set (Fin N → D.host.E)) Bm →
    ∃ g : Matrix (Fin N) (Fin N) ℂ_[p], (∀ a b, ‖g a b‖ ≤ 1) ∧ ‖g.det‖ = 1 ∧
      Bs = (Bm : Matrix (Fin N) (Fin N) D.host.E).map (TaylorLogMetric.tauEmb D lam τ) * g := by
  intro D p _ lam τ N L Bm Bs hR hL
  have hm : ∀ x, TaylorLogMetric.embT D τ x ∈ TaylorLogMetric.Qbar := fun x =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (TaylorLogMetric.embT D τ).toRatAlgHom)
  set ρ : D.host.E →+* ℂ_[p] := lam.comp ((TaylorLogMetric.embT D τ).codRestrict TaylorLogMetric.Qbar hm) with hρ
  have hρe : ∀ x, TaylorLogMetric.tauEmb D lam τ x = ρ x := fun x => dif_pos (hm x)
  have hint : ∀ y : 𝓞 D.host.E, ‖ρ (y : D.host.E)‖ ≤ 1 := fun y =>
    norm_le_one_of_isIntegral_int (map_isIntegral_int ρ y.isIntegral_coe)
  have hunit : ∀ s : ℕ, ¬ p ∣ s → ‖ρ (s : D.host.E)‖ = 1 := fun s hs => by
    rw [map_natCast]; exact norm_natCast_of_not_dvd hs
  set Mm : Matrix (Fin N) (Fin N) D.host.E := (Bm : Matrix (Fin N) (Fin N) D.host.E) with hMm
  set Mi : Matrix (Fin N) (Fin N) D.host.E := ((Bm⁻¹ : GL (Fin N) D.host.E) : Matrix (Fin N) (Fin N) D.host.E) with hMi
  have hMMi : Mm * Mi = 1 := Bm.mul_inv
  have hMiM : Mi * Mm = 1 := Bm.inv_mul
  set A : Matrix (Fin N) (Fin N) ℂ_[p] := Mm.map ρ with hA
  set Ai : Matrix (Fin N) (Fin N) ℂ_[p] := Mi.map ρ with hAi
  have hAAi : A * Ai = 1 := by
    simp only [hA, hAi, ← RingHom.mapMatrix_apply, ← map_mul, hMMi, map_one]
  have hAiA : Ai * A = 1 := by
    simp only [hA, hAi, ← RingHom.mapMatrix_apply, ← map_mul, hMiM, map_one]
  set g : Matrix (Fin N) (Fin N) ℂ_[p] := Ai * Bs with hg
  have hBs : Bs = A * g := by rw [hg, ← Matrix.mul_assoc, hAAi, Matrix.one_mul]
  have hgi : ∀ a b, ‖g a b‖ ≤ 1 := by
    intro a b
    obtain ⟨n, r, x, hr, hx, hB⟩ := hR.2.2 b
    have e : g a b = ∑ k, r k * ρ ((Mi *ᵥ x k) a) := by
      simp only [hg, Matrix.mul_apply, hB, hρe, hAi, Matrix.map_apply, Matrix.mulVec, dotProduct, map_sum,
        map_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [e]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
    obtain ⟨s, hs, hmem⟩ := (hL (x k)).1 ⟨1, (Fact.out : p.Prime).not_dvd_one, by simpa using hx k⟩
    obtain ⟨z, hz⟩ := hmem a
    have h1 : ‖ρ ((s : D.host.E) * (Mi *ᵥ x k) a)‖ ≤ 1 := by rw [← hz]; exact hint z
    rw [map_mul, norm_mul, hunit s hs, one_mul] at h1
    rw [norm_mul]
    calc ‖r k‖ * ‖ρ ((Mi *ᵥ x k) a)‖ ≤ 1 * 1 := by gcongr; exact hr k
      _ = 1 := one_mul 1
  have hBsu : IsUnit Bs.det := isUnit_iff_ne_zero.2 hR.1
  set h : Matrix (Fin N) (Fin N) ℂ_[p] := Bs⁻¹ * A with hh
  have hgh : g * h = 1 := by
    rw [hg, hh, Matrix.mul_assoc, ← Matrix.mul_assoc Bs, Matrix.mul_nonsing_inv _ hBsu, Matrix.one_mul, hAiA]
  have hhi : ∀ a b, ‖h a b‖ ≤ 1 := by
    intro a b
    set xb : Fin N → D.host.E := fun j => Mm j b with hxb
    have hcol : ∀ a, (Mi *ᵥ xb) a = (1 : Matrix (Fin N) (Fin N) D.host.E) a b := by
      intro a; rw [← hMiM]; rfl
    obtain ⟨s, hs, hmem⟩ := (hL xb).2 ⟨1, (Fact.out : p.Prime).not_dvd_one, fun a => by
      rw [hcol, Nat.cast_one, one_mul, Matrix.one_apply]
      split_ifs
      · exact ⟨1, map_one _⟩
      · exact ⟨0, map_zero _⟩⟩
    have hb := hR.2.1 _ hmem a
    have key : (Bs⁻¹ *ᵥ fun i => TaylorLogMetric.tauEmb D lam τ (((s : D.host.E) • xb) i)) a = ρ s * h a b := by
      simp only [hρe, Pi.smul_apply, smul_eq_mul, map_mul, hh, Matrix.mul_apply, Matrix.mulVec, dotProduct,
        hA, Matrix.map_apply, hxb, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [key, norm_mul, map_natCast, norm_natCast_of_not_dvd hs, one_mul] at hb
    exact hb
  have hd1 := norm_det_le_one g hgi
  have hd2 := norm_det_le_one h hhi
  have hprod : ‖g.det‖ * ‖h.det‖ = 1 := by
    rw [← norm_mul, ← Matrix.det_mul, hgh, Matrix.det_one, norm_one]
  refine ⟨g, hgi, le_antisymm hd1 ?_, ?_⟩
  swap
  · rw [hBs]; congr 1; ext i j; simp only [hA, Matrix.map_apply, hρe]
  calc (1 : ℝ) = ‖g.det‖ * ‖h.det‖ := hprod.symm
    _ ≤ ‖g.det‖ * 1 := by gcongr
    _ = ‖g.det‖ := mul_one _

end GlobalTheory.LocBasisChange

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemIffRead
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TypeRead

section Read

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {u : B.Word} {j : ℕ} {Ch : Type} {chOf : (I.stp u I.mu0 j).Cl → Ch}
  {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N j) → B.host.E)} {U : Ch → Subgroup (GA B (B.R.N j))} {chi : ∀ β, U β →* ℂˣ}
  {y : (I.stp u I.mu0 j).Cl → GA B (B.R.N j)} {st : ∀ c, (I.stp u I.mu0 j).Stab c → GL (Fin (B.R.N j)) B.host.E}
  {k : Ch → GA B (B.R.N j)}

set_option maxHeartbeats 2000000 in

theorem mem_iff_read (H : I.Reads u I.mu0 j chOf Lb U chi y st k) (c : (I.stp u I.mu0 j).Cl) (x : GA B (B.R.N j))
    (hx : x ∈ UAd B.sp.cm (B.R.N j)) :
    x ∈ U (chOf c) ↔ ∃ (hJ : x ∈ J0 B.sp.cm (B.R.N j) ((B.primes X).vT u))
      (hm : (redG B.sp.cm (B.R.N j) ((B.primes X).vT u) (B.primes X).vGs ⟨x, hJ⟩)⁻¹ ∈
        (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) j c.1).grp),
      cosetIn ((I.stp u I.mu0 j).act c.1 (1, ⟨_, hm⟩, 1) ((I.stp u I.mu0 j).rep c)) = cosetIn ((I.stp u I.mu0 j).rep c) := by
  constructor
  · intro hxU
    obtain ⟨q, hq⟩ := OneLevel.pt_exists I.twistPrimes_reference_tuple_eq_empty (OneLevel.reads_base H (chOf c)) (OneLevel.reads_pt H c) hx
    obtain ⟨κ, h1, h2, h3⟩ := (H.lev c x q hq).1 hxU
    subst h2
    obtain ⟨γ, h, θ⟩ := κ
    obtain rfl : γ = 1 := Subtype.ext ((toGLm B.fields.E (B.R.N j)).injective (h1.trans (map_one _).symm))
    obtain ⟨hJ, hr⟩ := OneLevel.pt_read I.twistPrimes_reference_tuple_eq_empty (OneLevel.reads_base H (chOf c)) (OneLevel.reads_pt H c) h.1 θ.1 hq
    obtain rfl : θ = 1 := Subtype.ext (funext fun P => (Finset.eq_empty_iff_forall_notMem.1 I.twistPrimes_reference_tuple_eq_empty P.1 P.2).elim)
    refine ⟨hJ, hr ▸ h.2, ?_⟩
    have e : (⟨_, hr ▸ h.2⟩ : (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) j c.1).grp) = h := Subtype.ext hr
    rw [e]
    exact h3
  · rintro ⟨hJ, hm, hc⟩
    exact OneLevel.mem_of_read H c x hJ hm hc

end Read

end GlobalTheory.Mem.Col2.TypeRead

namespace GlobalTheory.Mem.Col2.TypeRead

section Put

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E))

theorem put_mem_J0 (v : HeightOneSpectrum (𝓞 F)) (hT : v ∉ plUnder F ST) (x : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hx : x ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST)) : rll_put n v x ∈ J0 hc n ST := by
  have hxU : x ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) := hx.1
  have hxS : x ∈ stabGL (Formalism.L2.Herm.locL v (stdLat E n)) := by
    rw [← rll_locL_base n ST v hT]; exact hx.2
  have hS := rll_put_mem_St n v hxS
  refine (mem_mirabolicLevel_iff_reduction hc n ST).2 ⟨rll_put_mem_UAd hc n v hxU, hS, fun P hP => ?_⟩
  rw [rll_put_red n v x hS P (fun h => hT ⟨P, hP, h⟩)]
  exact Subgroup.one_mem _

theorem red_put_off (v : HeightOneSpectrum (𝓞 F)) (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hJ : rll_put n v x ∈ J0 hc n ST)
    (w : SG) (hw : ¬ IsOver v w.1) : redG hc n ST SG ⟨rll_put n v x, hJ⟩ w = 1 :=
  rll_put_red n v x (congruence_subgroup_le_stabilizer hc n ST hJ) w.1 hw

theorem red_put_at {gp : Fin 2 → ℕ} (G : GLoc F E hc.sig gp) (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp a : 𝓞 F) ∈ v.asIdeal)
    (w : SG) (e : (𝓞 E ⧸ w.1.asIdeal) ≃+* kv F v)
    (hcomp : ∀ z : Formalism.L2.Herm.intAf F E, ∃ hz : G.phi a v h (prV (E := E) v z.1) ∈ v.adicCompletionIntegers F,
      IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hz⟩ = e (resS F w.1 z))
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hJ : rll_put n v x ∈ J0 hc n ST) :
    ((redG hc n ST SG ⟨rll_put n v x, hJ⟩ w : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)).map e =
      redM F v (G.mat a v h 1 x) := by
  have hcomp' : ∀ (z : Formalism.L2.Herm.intAf F E), ∃ hz : gloPhi v (G.sp a v h) (prV (E := E) v z.1) ∈ v.adicCompletionIntegers F,
      IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hz⟩ = e (resS F w.1 z) := hcomp
  have hw := GlobalTheory.Mem.LevStd.gloRho_zero_of_compat v (G.sp a v h) (G.sp_alg a v h) w.1 e hcomp'
  have hgE := GlobalTheory.Mem.LevStd.gloE_eq_of_compat v (G.sp a v h) (G.sp_alg a v h) w.1 e hcomp'
  have h1 := gco_red_map n v (G.sp a v h) (G.sp_alg a v h) w.1 hw (congruence_subgroup_le_stabilizer hc n ST hJ)
  have hG : G.mat a v h 1 x = ((bc (gloPhi v (G.sp a v h)) (bc (prV (E := E) v) (rll_put n v x)) : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
    rw [rll_put_self]; simp only [GLoc.mat, inv_one, one_mul, mul_one]; rfl
  rw [hG, ← h1]
  ext i j
  rw [Matrix.map_apply, Matrix.map_apply, hgE]
  rfl

end Put

end GlobalTheory.Mem.Col2.TypeRead

namespace GlobalTheory.Mem.Col2.TypeRead

section Coset

variable {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}

def cvec (p : PtAt R sel mu cst u j) (P : rowSG Pr sel mu) : Fin (R.N j) → 𝓞 X.E ⧸ P.1.asIdeal :=
  redV P.1 ((qOf P.1 : X.E) • Classical.epsilon fun z => z ∈ cosetIn p P)

end Coset

end GlobalTheory.Mem.Col2.TypeRead

namespace GlobalTheory.Mem.Col2.TypeRead

section Fix

variable {K L : Type} [CommRing K] [CommRing L] {n : ℕ}

theorem fix_inv_iff (M : GL (Fin n) K) (c : Fin n → K) :
    ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ c = c ↔ (M : Matrix (Fin n) (Fin n) K) *ᵥ c = c := by
  constructor
  · intro h
    conv_lhs => rw [← h]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  · intro h
    conv_lhs => rw [← h]
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem fix_map_iff (e : K ≃+* L) (M : Matrix (Fin n) (Fin n) K) (c : Fin n → K) :
    M.map e *ᵥ (fun i => e (c i)) = (fun i => e (c i)) ↔ M *ᵥ c = c := by
  have h : M.map e *ᵥ (fun i => e (c i)) = fun i => e ((M *ᵥ c) i) := by
    have := RingHom.map_mulVec (e : K →+* L) M c
    funext i
    exact (this i).symm
  rw [h]
  constructor
  · intro h'
    funext i
    exact e.injective (congrFun h' i)
  · intro h'
    rw [h']

end Fix

end GlobalTheory.Mem.Col2.TypeRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemPrimeOfInclEMemPlaceIdealIntegralAdelicSpan
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar

theorem mem_of_inclE_mem_wInt : ∀ (D : D7) (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (α : 𝓞 D.host.E),
    Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (X.ιE.symm (α : D.host.E)) ∈ GlobalTheory.Mem.SymChar.wInt X w →
      α ∈ w.asIdeal := by
  intro D X w α hα
  set e : 𝓞 X.B.I.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv X.ιE with he
  set Wx : Ideal (𝓞 X.B.I.E) := w.asIdeal.comap (e : 𝓞 X.B.I.E →+* 𝓞 D.host.E) with hWx
  have hWx0 : Wx ≠ ⊥ := by
    intro h0
    apply w.ne_bot
    rw [eq_bot_iff]
    intro b hb
    have : e.symm b ∈ Wx := by
      show e (e.symm b) ∈ w.asIdeal
      simpa using hb
    rw [h0, Ideal.mem_bot] at this
    rw [Ideal.mem_bot]
    simpa using congrArg e this

  have key : ∀ c ∈ GlobalTheory.Mem.SymChar.wInt X w,
      ∃ h : c ∈ Formalism.L2.Herm.intAf X.B.I.F X.B.I.E,
        (⟨c, h⟩ : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E) ∈ Formalism.L2.DIV.idS X.B.I.F Wx := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨a, ⟨b, hb, hab⟩, rfl⟩ := hc
      refine ⟨(Formalism.L2.DIV.oToS X.B.I.F X.B.I.E a).2, ?_⟩
      have ha : a ∈ Wx := by
        show e a ∈ w.asIdeal
        have : e a = b := Subtype.ext hab
        rw [this]; exact hb
      exact Ideal.mem_map_of_mem _ ha
    | zero => exact ⟨zero_mem _, zero_mem _⟩
    | add x y _ _ hx hy =>
      obtain ⟨hx1, hx2⟩ := hx
      obtain ⟨hy1, hy2⟩ := hy
      exact ⟨add_mem hx1 hy1, add_mem hx2 hy2⟩
    | smul r x _ hx =>
      obtain ⟨hx1, hx2⟩ := hx
      refine ⟨mul_mem r.2 hx1, ?_⟩
      have : (⟨r • x, mul_mem r.2 hx1⟩ : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E) = ⟨r.1, r.2⟩ * ⟨x, hx1⟩ := rfl
      rw [this]
      exact Ideal.mul_mem_left _ _ hx2
  obtain ⟨h1, h2⟩ := key _ hα
  set c : 𝓞 X.B.I.E := e.symm α with hc
  have hoc : (⟨_, h1⟩ : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E) = Formalism.L2.DIV.oToS X.B.I.F X.B.I.E c := rfl
  rw [hoc] at h2
  have hz : Formalism.L2.DIV.cmpS X.B.I.F Wx (Ideal.Quotient.mk Wx c) = Formalism.L2.DIV.cmpS X.B.I.F Wx 0 := by
    rw [map_zero]
    show Ideal.Quotient.mk _ (Formalism.L2.DIV.oToS X.B.I.F X.B.I.E c) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 h2
  have hcW : c ∈ Wx := Ideal.Quotient.eq_zero_iff_mem.1 (Formalism.L2.DIV.cmpS_inj Wx hWx0 hz)
  have : e c = α := by rw [hc]; exact e.apply_symm_apply α
  rw [← this]
  exact hcW

end GlobalTheory.Mem.SymChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneSubEwMem
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SymChar.Resid

open GlobalTheory.Mem.SymFrame

variable {D : D7}

theorem rank_eq (D : D7) : D.R.r = D.R.k + 2 * D.R.rS + 1 := by
  unfold Ranks.r Ranks.rS
  obtain ⟨t, ht⟩ := D.R.m_even
  have := D.R.two_le_m
  omega

def posE (D : D7) (a : Fin D.R.rS) : Fin D.R.r := ⟨a.1, by have := rank_eq D; omega⟩

def posB (D : D7) (i : Fin D.R.k) : Fin D.R.r := ⟨D.R.rS + i.1, by have := rank_eq D; omega⟩

def posN (D : D7) (a : Fin D.R.rS) : Fin D.R.r :=
  ⟨if a.1 + 1 < D.R.rS then a.1 + 1 else D.R.rS + D.R.k, by have := rank_eq D; split_ifs <;> omega⟩

theorem symVec_posN (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (a : Fin D.R.rS) :
    symVec X w (posN D a) = nxt X.e0 X.z0 a := by
  unfold symVec GlobalTheory.SeeConjRead.flagV posN nxt
  by_cases h : a.1 + 1 < D.R.rS
  · simp [h]
  · have h2 : ¬ (D.R.rS + D.R.k < D.R.rS) := by omega
    simp [h]

theorem symVec_posB (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : EwAt X w) (i : Fin D.R.k) :
    symVec X w (posB D i) = X.bw i := by
  unfold symVec GlobalTheory.SeeConjRead.flagV posB epsW
  have h1 : ¬ (D.R.rS + i.1 < D.R.rS) := by omega
  have h2 : D.R.rS + i.1 < D.R.rS + D.R.k := by omega
  simp [h1, h2, hw]

theorem dual_row (X : HidaSetting D) (w : HeightOneSpectrum (𝓞 D.host.E)) {g : ℕ} {u : Fin D.R.r → VA X.B.I}
    {x : X.B.I.Gf} {N : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod g)} (hN : IsMatIn X w u x N)
    {y : VA X.B.I} (hy : y ∈ X.B.I.Lf) (i₀ : Fin D.R.r)
    (hd : ∀ j, hA X.B.I y (u j) - (if j = i₀ then 1 else 0) ∈ wInt X w) (i : Fin D.R.r) :
    hA X.B.I y (X.B.I.fmat x *ᵥ u i) - (((N i₀ i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈
      wInt X w := by
  have h := hA_isMatIn X w hN hy i
  have hs : (∑ j, (((N j i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) *
      (hA X.B.I y (u j) - (if j = i₀ then 1 else 0))) ∈ wInt X w := by
    refine Submodule.sum_mem _ fun j _ => ?_
    exact (wInt X w).smul_mem
      (⟨_, natCast_mem _ (N j i).val⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) (hd j)
  have e : (∑ j, (((N j i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) *
      (hA X.B.I y (u j) - (if j = i₀ then 1 else 0))) =
      (∑ j, (((N j i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * hA X.B.I y (u j)) -
        (((N i₀ i).val : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) := by
    simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  rw [e] at hs
  have := add_mem h hs
  convert this using 1
  abel

theorem natCast_g_mem (X : HidaSetting D) {w : HeightOneSpectrum (𝓞 D.host.E)} (k : Fin 2)
    (hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) :
    ((D.host.g k : ℕ) : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) ∈ wInt X w := by
  refine Submodule.subset_span ⟨(D.host.g k : 𝓞 X.B.I.E), ⟨_, hg, ?_⟩, ?_⟩
  · simp
  · simp

theorem one_sub_ew_mem (X : HidaSetting D) {w : HeightOneSpectrum (𝓞 D.host.E)} (k : Fin 2)
    (hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal) (hw : EwAt X w) : 1 - X.ew ∈ wInt X w := by
  have hz : X.z0 ∈ X.B.I.Lf := X.vectorsInLattice.2.1
  have h1 := hA_mem_wInt X w hz (hw X.z0 hz)
  rw [hA_smul_right'] at h1
  have h2 := wInt_of_zmod X k hg X.formsAtZero.1
  have hint : 1 - X.ew ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E := sub_mem (one_mem _) X.ew_int
  have h3 : (1 - X.ew) * (hA X.B.I X.z0 X.z0 + 1) ∈ wInt X w :=
    (wInt X w).smul_mem (⟨_, hint⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) h2
  have := sub_mem h3 h1
  convert this using 1
  ring

end GlobalTheory.Mem.SymChar.Resid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlacesOverTypePrimeChosenAndConj
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlacesOverG

theorem isConjPl_cP {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E)) :
    Formalism.BasicNotions.IsConjPl D.host P (GlobalTheory.IdemSupport.cP (D := D) P) := by
  intro x y hxy
  have hy : y = GlobalTheory.IdemSupport.cO D x := by
    apply RingOfIntegers.ext
    rw [hxy, GlobalTheory.IdemSupport.cO_coe]
    exact (Formalism.BasicNotions.bridge_star_holds D.R D.host _).symm
  rw [GlobalTheory.IdemSupport.mem_cP, hy, GlobalTheory.IdemSupport.cO_cO]

theorem conjPrime_conjPrime₂ {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E)) :
    GlobalTheory.IdemSupport.cP (D := D) (GlobalTheory.IdemSupport.cP (D := D) P) = P := by
  apply HeightOneSpectrum.ext
  ext x
  rw [GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.cO_cO]

theorem finrank_E' (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  have h1 : Module.finrank ℚ D.host.E = 4 * D.R.ord := D.host.finrank_cmField
  have h5 : D.R.f = 2 * D.R.ord := rfl
  rw [h1, h5]; ring

theorem places_over_g_k : ∀ (D : D7) (k : Fin 2), Function.Injective (Sum.elim (D.naut.plGw k) (fun v => GlobalTheory.IdemSupport.cP (D := D) (D.naut.plGw k v))) ∧ (∀ W : HeightOneSpectrum (𝓞 D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ W.asIdeal ↔ ∃ i, Sum.elim (D.naut.plGw k) (fun v => GlobalTheory.IdemSupport.cP (D := D) (D.naut.plGw k v)) i = W) ∧ Fintype.card (D.nd.PlG k ⊕ D.nd.PlG k) = Module.finrank ℚ D.host.E := by
  intro D k
  set f := Sum.elim (D.naut.plGw k) (fun v => GlobalTheory.IdemSupport.cP (D := D) (D.naut.plGw k v)) with hf
  have hne : ∀ v v', D.naut.plGw k v ≠ GlobalTheory.IdemSupport.cP (D := D) (D.naut.plGw k v') := fun v v' e =>
    D.naut.plGw_nconj k v' v (e ▸ isConjPl_cP _)
  have hinj : Function.Injective f := by
    rintro (a | a) (b | b) e
    · simp only [hf, Sum.elim_inl] at e; rw [D.naut.plGw_inj k e]
    · simp only [hf, Sum.elim_inl, Sum.elim_inr] at e; exact absurd e (hne a b)
    · simp only [hf, Sum.elim_inl, Sum.elim_inr] at e; exact absurd e.symm (hne b a)
    · simp only [hf, Sum.elim_inr] at e
      have := congrArg (GlobalTheory.IdemSupport.cP (D := D)) e
      rw [conjPrime_conjPrime₂, conjPrime_conjPrime₂] at this
      rw [D.naut.plGw_inj k this]
  have hmem : ∀ i, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (f i).asIdeal := by
    rintro (v | v)
    · exact D.naut.plGw_over k v
    · show _ ∈ (GlobalTheory.IdemSupport.cP (D := D) (D.naut.plGw k v)).asIdeal
      rw [GlobalTheory.IdemSupport.mem_cP, map_natCast]
      exact D.naut.plGw_over k v
  have hcard : Fintype.card (D.nd.PlG k ⊕ D.nd.PlG k) = Module.finrank ℚ D.host.E := by
    rw [Fintype.card_sum, D.nd.card_PlG k, finrank_E', two_mul]
  refine ⟨hinj, fun W => ⟨fun hW => ?_, ?_⟩, hcard⟩
  · have hfin : (Formalism.BasicNotions.placesOver D.host.E (D.host.g k)).Finite := by
      apply Set.finite_of_ncard_ne_zero
      rw [D.nd.g_split k]; exact Module.finrank_pos.ne'
    have hsub : Set.range f ⊆ Formalism.BasicNotions.placesOver D.host.E (D.host.g k) := by
      rintro _ ⟨i, rfl⟩; exact hmem i
    have hle : (Formalism.BasicNotions.placesOver D.host.E (D.host.g k)).ncard ≤ (Set.range f).ncard := by
      rw [D.nd.g_split k, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, hcard]
    have heq := Set.eq_of_subset_of_ncard_le hsub hle hfin
    have : W ∈ Set.range f := by rw [heq]; exact hW
    exact this
  · rintro ⟨i, rfl⟩; exact hmem i

end GlobalTheory.PlacesOverG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalNormOneClassEqFiniteAdelicDetClassStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalNormOne_class_eq_finiteAdelic_det_class : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) (z : unitary H.E) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)), Matrix.GeneralLinearGroup.det x.1 = Formalism.L2.Herm.unitaryOneRationalAdele H.F z → e1Q H SQ z = u1Dt H SQ x := by
  first | exact @GlobalTheory.Mem.Col2.FullDt.e1Q_eq_u1Dt_of_det_eq | exact GlobalTheory.Mem.Col2.FullDt.e1Q_eq_u1Dt_of_det_eq | (intros; apply GlobalTheory.Mem.Col2.FullDt.e1Q_eq_u1Dt_of_det_eq <;> assumption)
end

