import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0265
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0461
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0075
import Formalism.LocalToGlobal.Columns.ChainTw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
import Formalism.LocalToGlobal.GroupLattices.StabilizerCount.StabiliserTrivialOfTiedChain
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThetaLocalEquivalence.ThEquivPStepCIff

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RationalIsometryOrthonormalMatrixUnitary
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV

open Matrix

section Gen

variable {E : Type} [Field E] {N : ℕ}

theorem unit_hform_mulVec (σ : E →+* E) (J B : Matrix (Fin N) (Fin N) E) (x y : Fin N → E) :
    hform σ J (B *ᵥ x) (B *ᵥ y) = hform σ (cT σ B * J * B) x y := by
  have key : ∀ (K : Matrix (Fin N) (Fin N) E) (v w : Fin N → E), hform σ K v w = (σ ∘ v) ⬝ᵥ (K *ᵥ w) := by
    intro K v w
    simp [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have h1 : σ ∘ (B *ᵥ x) = (B.map σ) *ᵥ (σ ∘ x) := funext fun l => RingHom.map_mulVec σ B x l
  rw [key, key, h1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (σ ∘ x), cT,
    Matrix.vecMul_transpose]

theorem unit_hform_one (σ : E →+* E) (x y : Fin N → E) : hform σ 1 x y = ∑ a, σ (x a) * y a := by
  simp [hform, Matrix.one_apply]

theorem cT_mul_self_of_hform (σ : E →+* E) (M : Matrix (Fin N) (Fin N) E)
    (h : ∀ x y, hform σ 1 (M *ᵥ x) (M *ᵥ y) = hform σ 1 x y) : cT σ M * M = 1 := by
  ext p q
  have h1 := h (Pi.single p 1) (Pi.single q 1)
  rw [unit_hform_mulVec, Matrix.mul_one] at h1
  simpa [hform, Pi.single_apply, apply_ite σ] using h1

end Gen

section Gen2

variable {E : Type} [Field E] {N : ℕ}

theorem cT_mul_self_toStdCo_stdG (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (co γ : GL (Fin N) E)
    (hco : cT σ co.1 * co.1 = J) (hγ : γ ∈ UJ σ J) :
    cT σ (LinearMap.toMatrix' ((toStdCo σ J co).trans (stdG σ J γ)).toLinearMap) *
      LinearMap.toMatrix' ((toStdCo σ J co).trans (stdG σ J γ)).toLinearMap = 1 := by
  have hc : IsOrthCo σ J (toLE co) := by
    intro x y
    have h := unit_hform_mulVec σ 1 co.1 x y
    rw [Matrix.mul_one, hco, unit_hform_one] at h
    exact h
  have hs : IsOrthCo σ J (stdCo σ J) := Classical.epsilon_spec (p := IsOrthCo σ J) ⟨_, hc⟩
  have hγ' : cT σ γ.1 * J * γ.1 = J := hγ
  apply cT_mul_self_of_hform
  intro x y
  rw [LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec, unit_hform_one, unit_hform_one]
  obtain ⟨x, rfl⟩ := (toLE co).surjective x
  obtain ⟨y, rfl⟩ := (toLE co).surjective y
  rw [hc]
  simp only [toStdCo, stdG, LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rw [hs]
  have h := unit_hform_mulVec σ J γ.1 x y
  rw [hγ'] at h
  exact h

end Gen2

theorem ratIsometry_unitary : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i (hi : i ≤ D.R.m), ∀ γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi), (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (A.crd i hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) γ)).toLinearMap) * star (LinearMap.toMatrix' ((toStdCo (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (A.crd i hi)).trans (stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) γ)).toLinearMap) = 1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP _ i hi γ hγ
  have h := cT_mul_self_toStdCo_stdG (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D i hi) (A.crd i hi) γ (hP.crd_orth i hi) hγ
  rw [mul_eq_one_comm] at h
  exact h

end GlobalTheory.TwV

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealSubfieldHeckeCharFinitePartEqOne
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host
open GlobalTheory.HeckeUnrExt
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap ideleConj finiteCompletionMap)

namespace GlobalTheory.HeckeFinTriv

theorem valued_natCast_le_one {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Valued.v (n : v.adicCompletion K) ≤ 1 := by
  induction n with
  | zero => rw [Nat.cast_zero, map_zero]; exact zero_le
  | succ n ih =>
    rw [Nat.cast_succ]
    exact Valuation.map_add_le _ ih (by rw [map_one])

theorem valued_natCast_le_of_dvd {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {M N : ℕ}
    (h : M ∣ N) : Valued.v (N : v.adicCompletion K) ≤ Valued.v (M : v.adicCompletion K) := by
  obtain ⟨k, rfl⟩ := h
  rw [Nat.cast_mul, map_mul]
  exact mul_le_of_le_one_right' (valued_natCast_le_one v k)

theorem finPart_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ψ : HChar (maximalRealSubfield E)) (M : ℕ), (∀ a : Ideles (maximalRealSubfield E), a ∈ GlobalTheory.Mem.Chr.unitIdl (maximalRealSubfield E) → (∀ w, (a : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).1 w = 1) → (∀ P : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), Valued.v ((a : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).2 P - 1) ≤ Valued.v ((M : maximalRealSubfield E) : P.adicCompletion (maximalRealSubfield E))) → ψ.1 a = 1) → (∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w → ψ.UnrAt (w.under (𝓞 (maximalRealSubfield E)))) → ∀ (w₀ : HeightOneSpectrum (𝓞 E)) (N : ℕ), M ∣ N → ∀ b : Ideles (maximalRealSubfield E), ideleMap (maximalRealSubfield E) E b ∈ levT E {w | GlobalTheory.UnitaryBC.IsSplitAt w ∧ w ≠ w₀} N → ψ.1 (GlobalTheory.Mem.Chr.finPartI (maximalRealSubfield E) b) = 1 := by
  intro E _ _ _ ψ M hlev hns w₀ N hMN b hb
  have he : ∀ w : HeightOneSpectrum (𝓞 E), (w.under (𝓞 (maximalRealSubfield E))).asIdeal.ramificationIdx' w.asIdeal ≠ 0 := fun w =>
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal (w.under (𝓞 (maximalRealSubfield E))).ne_bot
  have hc : ∀ w : HeightOneSpectrum (𝓞 E), (ideleMap (maximalRealSubfield E) E b).val.2 w =
      finiteCompletionMap (maximalRealSubfield E) E w (b.val.2 (w.under (𝓞 (maximalRealSubfield E)))) := fun w => rfl
  have hs : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) = v := fun v => by
    haveI := v.isPrime
    obtain ⟨⟨P, hP, hP'⟩⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 E)))
    exact ⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, HeightOneSpectrum.ext hP'.over.symm⟩

  have hunit : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), Valued.v (b.val.2 v) = 1 := fun v => by
    obtain ⟨w, rfl⟩ := hs v
    have h := hb.1 w
    change Valued.v ((ideleMap (maximalRealSubfield E) E b).val.2 w) = 1 at h
    rw [hc, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap, pow_eq_one_iff_of_nonneg zero_le (he w)] at h
    exact h

  have hcong : ∀ w : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w → w ≠ w₀ →
      Valued.v (b.val.2 (w.under (𝓞 (maximalRealSubfield E))) - 1) ≤ Valued.v (N : (w.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) := fun w h1 h2 => by
    have h := hb.2 w ⟨h1, h2⟩
    change Valued.v ((ideleMap (maximalRealSubfield E) E b).val.2 w - 1) ≤ _ at h
    rwa [hc, ← map_one (finiteCompletionMap (maximalRealSubfield E) E w), ← map_sub, ← map_natCast (finiteCompletionMap (maximalRealSubfield E) E w),
      GlobalTheory.UpIdeleMod.valued_finiteCompletionMap, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap,
      pow_le_pow_iff_left₀ zero_le zero_le (he w)] at h
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local (maximalRealSubfield E) ψ.1 ψ.2.1 (GlobalTheory.Mem.Chr.finPartI (maximalRealSubfield E) b)
    (GlobalTheory.Mem.Chr.finPartI_mem_unitIdl.2 hunit) (fun w => by rw [GlobalTheory.Mem.Chr.finPartI_fst]; rfl) ?_
  intro v x hx
  rw [GlobalTheory.Mem.Chr.finPartI_snd] at hx
  have hxu : Valued.v (x : v.adicCompletion (maximalRealSubfield E)) = 1 := by rw [hx]; exact hunit v
  by_cases hu : ψ.UnrAt v
  · exact hu x hxu
  obtain ⟨w, hw⟩ := hs v
  have hsp : GlobalTheory.UnitaryBC.IsSplitAt w := by
    by_contra hn
    exact hu (hw ▸ hns w hn)
  obtain ⟨u, hu1, hu2⟩ := hsp
  have hsp' : ∃ w' : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w' ∧ w' ≠ w₀ ∧ w'.under (𝓞 (maximalRealSubfield E)) = v := by
    by_cases h0 : w = w₀
    · refine ⟨u, ⟨w, fun e => hu1 e.symm, hu2.symm⟩, h0 ▸ hu1, hu2.trans hw⟩
    · exact ⟨w, ⟨u, hu1, hu2⟩, h0, hw⟩
  obtain ⟨w', hw'1, hw'2, rfl⟩ := hsp'
  have hxc : Valued.v ((x : (w'.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) - 1) ≤
      Valued.v ((M : (maximalRealSubfield E)) : (w'.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) := by
    rw [hx]
    refine (hcong w' hw'1 hw'2).trans ?_
    have e : ((M : (maximalRealSubfield E)) : (w'.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) = (M : (w'.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) := by
      rw [← map_natCast (algebraMap (maximalRealSubfield E) ((w'.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E))) M]; rfl
    rw [e]
    exact valued_natCast_le_of_dvd _ hMN
  apply hlev
  · intro P
    by_cases hP : P = w'.under (𝓞 (maximalRealSubfield E))
    · subst hP
      rw [GlobalTheory.HeckeProduct.localIdele_snd_self]
      exact hxu
    · rw [GlobalTheory.HeckeProduct.localIdele_snd_ne (maximalRealSubfield E) _ _ hP]
      exact map_one _
  · intro w
    rw [GlobalTheory.HeckeProduct.localIdele_fst]
    rfl
  · intro P
    by_cases hP : P = w'.under (𝓞 (maximalRealSubfield E))
    · subst hP
      rw [GlobalTheory.HeckeProduct.localIdele_snd_self]
      exact hxc
    · rw [GlobalTheory.HeckeProduct.localIdele_snd_ne (maximalRealSubfield E) _ _ hP, sub_self, map_zero]
      exact zero_le

end GlobalTheory.HeckeFinTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardKernelDataWithStandardBaseLevels
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Pdv.stdKer_stdRd : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKer l Z t → ∃ t' : KerEntTied ex, I.StdKer l Z t' ∧ GlobalTheory.Pdv.StdRd I l Z t' ∧ t'.TopPinned := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex t hS
  rcases t with ⟨cc, cc_rec, cc_ok, δ, δ_ok, Bb, χ, χ_ok, idl, idl_ok, χ_rec, cD, Xf, seam, seam_ok, Pr, pr_ok, g_rec, Ch, sel, S, word, T_rec, tup, Q_rec, cst, idx, m2, glob, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th, unf, ent, ent_lam, kf, kf_un, served⟩
  obtain ⟨hX, hseam, hPr, hCh, hsel, hSS, hword, htup, hcst, hidx, hm2, hglob, hamb, hδ, hO⟩ := hS
  dsimp only at hX hseam hPr hCh hsel hSS hword htup hcst hidx hm2 hglob hamb hδ hO
  subst hX
  cases hseam
  cases hPr
  cases hCh
  cases hsel
  subst hSS
  cases htup
  cases hcst
  cases hidx
  subst hm2
  cases hglob
  cases hword
  have hA : ambOf (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) Bb χ cD = I.J.amb B χ := eq_of_heq hamb
  have hm := hOk.hm
  have hpi : ∀ (u : B.Word) (a : I.ι) (w : rowSG (B.primes X) I.sel (I.tup a)), (B.primes X).piT u ∉ w.1.asIdeal := fun u a =>
    (TopStep.tilOk_of_avoid l.pr hOk.sel_ok u ⟨hOk.T_mem u, hOk.g_mem⟩).2.1
  refine ⟨⟨cc, cc_rec, cc_ok, δ, δ_ok, Bb, χ, χ_ok, idl, idl_ok, χ_rec, cD, _, _, seam_ok, _, pr_ok, g_rec, _, _, _, _, T_rec, _, Q_rec, _, _, _, _, glob_σ, glob_xi, idx_ok, O, I.kerRd l Z, fun u a => topChain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (FieldsLaws.fields_ok B) l.pr (hOk.idx_ok a).cst_ok hm (hpi u a) (I.kerRd_top l Z hm u a), O_dgen, O_S, ?_, ?_, unf, ent, ent_lam, kf, kf_un, served⟩, ?_, ?_, ?_⟩
  · exact fun u a i c => (hO.lat u a i c).trans (seamOf_lat B (I.cols l) Z.W Z.V Z.S Z.N Z.G _).symm
  · intro u a i c c'
    rw [hA, AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J χ, χ_rec]
    exact (hO.Th u a i c c').trans (I.kerRd_Th l Z hOk idl_ok hO u a i c c').symm
  · exact ⟨rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, heq_of_eq hA, hδ, hO⟩
  · exact fun u a => ⟨I.kerRd l Z u a, HEq.rfl, fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  · exact fun u a => I.kerRd_top l Z hm u a
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StdKerStdRdMark
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Pdv.stdKer_stdRd_mark : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKer l Z t → ∃ t' : KerEntTied ex, I.StdKer l Z t' ∧ GlobalTheory.Pdv.StdRd I l Z t' ∧ t'.TopPinned ∧ (∀ (u : B.Word) (a : I.ι) (i : ℕ) (c : ((I.rec7 l Z).chTw u a).cls i), (t'.rd u a).pin i c ↔ (i + 1 ≤ B.R.m ∨ ∃ d, OverRow (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d ((I.stp u a i).rep c).1.1)) := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex t hS
  rcases t with ⟨cc, cc_rec, cc_ok, δ, δ_ok, Bb, χ, χ_ok, idl, idl_ok, χ_rec, cD, Xf, seam, seam_ok, Pr, pr_ok, g_rec, Ch, sel, S, word, T_rec, tup, Q_rec, cst, idx, m2, glob, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th, unf, ent, ent_lam, kf, kf_un, served⟩
  obtain ⟨hX, hseam, hPr, hCh, hsel, hSS, hword, htup, hcst, hidx, hm2, hglob, hamb, hδ, hO⟩ := hS
  dsimp only at hX hseam hPr hCh hsel hSS hword htup hcst hidx hm2 hglob hamb hδ hO
  subst hX
  cases hseam
  cases hPr
  cases hCh
  cases hsel
  subst hSS
  cases htup
  cases hcst
  cases hidx
  subst hm2
  cases hglob
  cases hword
  have hA : ambOf (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) Bb χ cD = I.J.amb B χ := eq_of_heq hamb
  have hm := hOk.hm
  have hpi : ∀ (u : B.Word) (a : I.ι) (w : rowSG (B.primes X) I.sel (I.tup a)), (B.primes X).piT u ∉ w.1.asIdeal := fun u a =>
    (TopStep.tilOk_of_avoid l.pr hOk.sel_ok u ⟨hOk.T_mem u, hOk.g_mem⟩).2.1
  refine ⟨⟨cc, cc_rec, cc_ok, δ, δ_ok, Bb, χ, χ_ok, idl, idl_ok, χ_rec, cD, _, _, seam_ok, _, pr_ok, g_rec, _, _, _, _, T_rec, _, Q_rec, _, _, _, _, glob_σ, glob_xi, idx_ok, O, I.kerRd l Z, fun u a => topChain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (FieldsLaws.fields_ok B) l.pr (hOk.idx_ok a).cst_ok hm (hpi u a) (I.kerRd_top l Z hm u a), O_dgen, O_S, ?_, ?_, unf, ent, ent_lam, kf, kf_un, served⟩, ?_, ?_, ?_, ?_⟩
  · exact fun u a i c => (hO.lat u a i c).trans (seamOf_lat B (I.cols l) Z.W Z.V Z.S Z.N Z.G _).symm
  · intro u a i c c'
    rw [hA, AmbIn.amb_eq_ambOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G I.J χ, χ_rec]
    exact (hO.Th u a i c c').trans (I.kerRd_Th l Z hOk idl_ok hO u a i c c').symm
  · exact ⟨rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl, heq_of_eq hA, hδ, hO⟩
  · exact fun u a => ⟨I.kerRd l Z u a, HEq.rfl, fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  · exact fun u a => I.kerRd_top l Z hm u a
  · exact fun u a i c => Iff.rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepRepEqOneAtTypePrimes
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Pdv

open Classical in

theorem stepRep_eq_one_at_typePrimes {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (m2 j : ℕ)
    (b : (twSt Ch sel mu cst m2 j).β) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) :
    (twSt Ch sel mu cst m2 j).h b P = 1 := by
  cases j with
  | zero => rfl
  | succ i =>
    by_cases h1 : i + 1 ≤ m2
    · revert b
      rw [show twSt Ch sel mu cst m2 (i+1) = twNext Ch sel mu cst (twSt Ch sel mu cst m2 i) by simp [twSt, h1]]
      intro b
      have hq : P.1 ∉ twQOff (Pr := Pr) sel mu := fun hq => (Finset.mem_sdiff.1 hq).2 hP
      simp only [twNext, hq, dif_neg, not_false_eq_true]
    · by_cases h2 : i + 1 = m2 + 1
      · revert b
        rw [show twSt Ch sel mu cst m2 (i+1) = twUnitSt _ (i+1) by simp [twSt, h1, h2]]
        intro b; rfl
      · revert b
        rw [show twSt Ch sel mu cst m2 (i+1) = twEmptySt _ (i+1) by simp only [twSt, if_neg h1, if_neg h2]]
        intro b; exact b.elim

theorem colNorm_of_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), (∀ a, I.cst a = twCst I.Ch I.sel (I.tup a) I.glob ∧ I.idx a = twIdx I.Ch I.sel (I.tup a) (I.cst a) (B.R.m - 2)) → GlobalTheory.Pdv.ColNorm I := by
  intro B X I H a
  obtain ⟨hc, hi⟩ := H a
  refine ⟨?_, ?_, ?_⟩
  · rw [hc]; show B.R.m ≤ B.R.m + 1; omega
  · rw [hc]; show B.R.m ≤ B.R.m; exact le_rfl
  · rw [hi]
    intro j _ b P hP
    exact stepRep_eq_one_at_typePrimes _ _ _ _ _ _ b P hP

end GlobalTheory.Pdv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroTrivialStabilisersTrueColumns
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Pdv.StabZero

open GlobalTheory.Mem.Col2.ClsZero

variable {B : Base} {X : PreX B.toPre} {I : TC B X}

theorem idx_empty (a : I.ι) (u : B.Word) {b : (I.stp u a 0).β} (p : (I.stp u a 0).D b) : p.1.2 = ∅ := by
  obtain ⟨⟨q, Y⟩, hY⟩ := p
  rw [ys0 a] at hY
  exact hY

theorem gam_eq_one (h : I.Ok) (u : B.Word) (a : I.ι)
    (hm : ∀ c' : (I.stp u I.mu0 0).Cl, Nat.card ((I.stp u I.mu0 0).Stab c') = 1)
    (c : (I.stp u a 0).Cl) (s : (I.stp u a 0).Stab c) : s.1.1 = 1 := by
  obtain ⟨b⟩ := stepZero_chartIndex_nonempty h a
  obtain ⟨c', rfl⟩ := (bij0 h u a b).2 c
  have hd := stepZero_corresponding_representatives_same_deco h u a b c'
  set p := (I.stp u a 0).rep (I.cl0 u a b c') with hp
  set p0 := (I.stp u I.mu0 0).rep c' with hp0
  have hs : _ = _ := s.2
  have hsd : ((s.1.1, (s.1.2.1.1 : GLG B.fields.E (B.R.N 0) (B.primes X).vGs)) : UF B.fields.E (B.R.N 0) × GLG B.fields.E (B.R.N 0) (B.primes X).vGs) • p.1.1.deco = p.1.1.deco :=
    congrArg (fun x => DecoF.deco x.1.1) hs
  rw [hd] at hsd
  have hγ : ∀ (P : HeightOneSpectrum (𝓞 B.fields.E)) (z : Sp B.fields.E (B.R.N 0)),
      s.1.1.1 z ∈ p0.1.1.deco.1.at P ↔ z ∈ p0.1.1.deco.1.at P := by
    intro P z
    have e := congrArg (fun d : DecoSet B.fields.E (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs => s.1.1.1 z ∈ d.1.at P) hsd
    simp only at e
    rw [← e]
    show s.1.1.1 z ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.HermitianLatticesTheory.gmap s.1.1.1 _) ↔ _
    rw [mem_localization_gmap, LinearEquiv.symm_apply_apply]
  have hc : ∀ P, ((p0.1.1.1.2 P)⁻¹ * (s.1.1.1 * p0.1.1.1.2 P)) ∈ GLint B.fields.E (B.R.N 0) P.1 := by
    intro P x
    show (p0.1.1.1.2 P).symm (s.1.1.1 (p0.1.1.1.2 P x)) ∈ stdAt _ _ P.1 ↔ x ∈ stdAt _ _ P.1
    rw [← p0.1.1.2 P, LinearEquiv.apply_symm_apply, ← p0.1.1.2 P x]
    exact hγ P.1 _
  let t : (I.stp u I.mu0 0).G c'.1 :=
    (s.1.1, ⟨s.1.2.1.1, by
      have e1 := levelTypePrimes_stepZero_eq_colLev h I.mu0 c'.1
      have e2 := levelTypePrimes_stepZero_eq_colLev h a b
      rw [e1, ← e2]
      exact s.1.2.1.2⟩,
     ⟨fun P => ⟨(p0.1.1.1.2 P)⁻¹ * (s.1.1.1 * p0.1.1.1.2 P), hc P⟩, by
      rw [chartIndexLevelTwistPrimes_stepZero_eq_top h I.mu0 c'.1]
      intro P _
      trivial⟩)
  let st : (I.stp u I.mu0 0).Stab c' := ⟨t, by
    show _ = _
    refine Subtype.ext (Prod.ext (Subtype.ext (Prod.ext hsd ?_)) ?_)
    · funext P
      show s.1.1.1 * p0.1.1.1.2 P * (⟨(p0.1.1.1.2 P)⁻¹ * (s.1.1.1 * p0.1.1.1.2 P), hc P⟩⁻¹ : ↥(GLint B.fields.E (B.R.N 0) P.1)).1 = p0.1.1.1.2 P
      simp only [Subgroup.coe_inv]
      group
    · show (fun v => s.1.1.1 v) '' p0.1.2 = p0.1.2
      rw [idx_empty I.mu0 u p0, Set.image_empty]⟩
  have hsub := (Nat.card_eq_one_iff_unique.1 (hm c')).1
  have e : st = 1 := Subsingleton.elim _ _
  exact congrArg (fun x : (I.stp u I.mu0 0).Stab c' => x.1.1) e

theorem card_stab_zero (h : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι)
    (hm : ∀ c' : (I.stp u I.mu0 0).Cl, Nat.card ((I.stp u I.mu0 0).Stab c') = 1) (c : (I.stp u a 0).Cl) :
    Nat.card ((I.stp u a 0).Stab c) = 1 := by
  have e : ∀ s : (I.stp u a 0).Stab c, s = 1 := fun s =>
    Subtype.ext (((l.ch u a).step 0).stab_inj c.1 s.1 _ s.2 (by
      change (ufGL _ _) s.1.1 = 1
      rw [gam_eq_one h u a hm c s, map_one]))
  exact Nat.card_eq_one_iff_unique.2 ⟨⟨fun s s' => (e s).trans (e s').symm⟩, ⟨1⟩⟩

end GlobalTheory.Pdv.StabZero

namespace GlobalTheory.Pdv

open GlobalTheory.Pdv.StabZero

theorem stepZero_trivial_stabilisers_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)),
    LevelData (I.rec7 l Z) → OrbitPlaces.Stab0 (I.rec7 l Z) := by
  intro B X I h _ l Z lev
  exact ⟨Formalism.L2.G.StabilizerCardinality.card_stab0_mem _ lev,
    fun u μ _ c => card_stab_zero h l u μ (fun c' => Formalism.L2.G.StabilizerCardinality.card_stab0_mem _ lev u c') c⟩

end GlobalTheory.Pdv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameLocalCharacterDetCongruentOneEqOne
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG

noncomputable section

namespace GlobalTheory.TwV.AwayCpl.RhoOne

open GlobalTheory.TopStep

theorem redGL_eq_one_of_cong {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}
    (D : ℕ) (hD : 1 ≤ D) (k : GLint E n P)
    (hk : ∀ s l, IntAt P ((((qOf P : ℕ) : E) ^ D)⁻¹ * (k.1 (Pi.single s 1) l - (Pi.single s 1 : Sp E n) l))) :
    redGL n P k = 1 := by
  apply Units.ext
  rw [redGL_val, Units.val_one]
  ext a b
  have hq := qOf_ne_zero (P := P)
  have hint : IntAt P ((k.1 (Pi.single b 1) a - (Pi.single b 1 : Sp E n) a) / ((qOf P : ℕ) : E)) := by
    obtain ⟨d, hd⟩ : ∃ d, D = d + 1 := ⟨D - 1, by omega⟩
    have e : (k.1 (Pi.single b 1) a - (Pi.single b 1 : Sp E n) a) / ((qOf P : ℕ) : E) =
        ((qOf P : ℕ) : E) ^ d * ((((qOf P : ℕ) : E) ^ D)⁻¹ * (k.1 (Pi.single b 1) a - (Pi.single b 1 : Sp E n) a)) := by
      rw [hd, pow_succ]
      field_simp
    rw [e]
    exact (intAt_pow (intAt_nat _) _).mul (hk b a)
  have h0 := redP_eq_zero_of_div hint
  have hs : IntAt P ((Pi.single b 1 : Sp E n) a) := mem_stdAt.1 (single_mem_stdAt b) a
  rw [reduction_sub (glint_entry k a b) hs, sub_eq_zero] at h0
  rw [redMat, Matrix.of_apply, h0]
  by_cases h : a = b
  · subst h
    simp [reduction_one₂]
  · simp [Pi.single_apply, h, reduction_zero]

theorem rhoS_det_one : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)), cst.Ok → ∀ (i n : ℕ) (P : rowSG Pr sel mu) (k : GLint X.E n P.1),
    (∀ s l, IntAt P.1 ((((qOf P.1 : ℕ) : X.E) ^ (cst.D P))⁻¹ * (k.1 (Pi.single s 1) l - (Pi.single s 1 : Sp X.E n) l))) →
    rhoS Ch sel mu i P ((LinearEquiv.det k.1 : X.Eˣ) : X.E) = 1 := by
  intro X Pr R Ch sel S mu cst hc i n P k hk
  have hred := redGL_eq_one_of_cong (cst.D P) (hc.D_pos P) k hk
  have hdet : redP P.1 ((LinearEquiv.det k.1 : X.Eˣ) : X.E) = 1 := by
    rw [(det_glint k).2, ← redGL_val, hred, Units.val_one, Matrix.det_one]
  unfold rhoS LocE.unitV
  rw [hdet]
  simp

end GlobalTheory.TwV.AwayCpl.RhoOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TransportedLatticesTwoClassesAdmissible
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

theorem adm_seam_lat_rd_pair : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) u μ i j c c', TaylorLogMetric.admitted D _ _ (t.seam.lat ((t.rd u μ).N i c)) (t.seam.lat ((t.rd u μ).N j c')) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ i j c c'
  rw [← t.O_lat, ← t.O_lat]
  exact ⟨Formalism.L2.Ker.even_rankN _ _, Formalism.L2.Ker.even_rankN _ _, ((t.O u μ).lat i c).2, ((t.O u μ).lat j c').2⟩

end GlobalTheory.TwV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiTopEqProd
section
noncomputable section

namespace GlobalTheory.TwTop

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

def topF {u : Pr.Word} (i : ℕ) (P : rowSG Pr sel mu) (p : ChPt (R := R) sel mu u i) (Y : Set (Sp X.E (R.N i)))
    (p' : ChPt (R := R) sel mu u (i + 1)) (x : HomE X.E (R.N i) (R.N (i + 1))) : X.K :=
  PhiTopG Ch mu cst.sharp i (i + 1) (R.N (i + 1)) P.1 (prXpG X.E (R.N (i + 1)) ∘ₗ inFr (frsF sel mu p P) (frsG sel mu p' P) x ∘ₗ
      LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R i))) *
    ftY sel mu cst P (atNL X.E (R.N (i + 1)) (R.N (i + 1) - 1) ∘ₗ inFr (frsF sel mu p P) (frsG sel mu p' P) x) ((frsF sel mu p P).symm (repY Y))

theorem xiTop_eq_prod {u : Pr.Word} (i : ℕ) (p : ChPt (R := R) sel mu u i) (Y : Set (Sp X.E (R.N i)))
    (p' : ChPt (R := R) sel mu u (i + 1)) (x : HomE X.E (R.N i) (R.N (i + 1))) :
    XiTop Ch sel mu cst i p Y p' x = phiT X.K p.deco.1 p'.deco.1 x * ∏ P, topF Ch sel mu cst i P p Y p' x := rfl

end GlobalTheory.TwTop

end
end

