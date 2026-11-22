import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2000
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1368
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0273
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2004
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergTranslateThetaContinuousDifferentiable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0116
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0331
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.IntegralOfMemIntAE
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitThetaGridIsAdmissibleFlipTensor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0586
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0657
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0554
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0574

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsArchimedeanIdentity
section
noncomputable section

namespace GlobalTheory.KStableLie

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_of_isExp {V : Type} [AddCommGroup V] [Module ℂ V] {L U : Module.End ℂ V} (hU : IsExp L U)
    (N : Submodule ℂ V) (hL : ∀ y ∈ N, L y ∈ N) {v : V} (hv : v ∈ N) : U v ∈ N := by
  have hpow : ∀ m : ℕ, (L ^ m) v ∈ N := by
    intro m
    induction m with
    | zero => simpa using hv
    | succ m ih => rw [pow_succ', Module.End.mul_apply]; exact hL _ ih
  by_contra hn
  obtain ⟨l, hl, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  have hz : ∀ y ∈ N, l y = 0 := fun y hy => by
    have h' := Submodule.mem_map_of_mem (f := l) hy
    rw [hmap, Submodule.mem_bot] at h'
    exact h'
  have h0 : (fun m : ℕ => ((m.factorial : ℂ))⁻¹ * l ((L ^ m) v)) = fun _ => 0 := by
    funext m; rw [hz _ (hpow m), mul_zero]
  have hs := hU v l
  rw [h0] at hs
  exact hl (hs.unique hasSum_zero)

open scoped Classical in

theorem kStable_of_lieStable (hP : GlobalTheory.FunPr.Hypotheses₂) {σ : E →ₐ[F] E} {B : Base F E} {n d : ℕ} {X : Spc F E n}
    {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ} (hb : B.IsGood σ)
    (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (hw : M.IsWeil B.ψ χX χW om) {Pi : Type} [AddCommGroup Pi]
    [Module ℂ Pi] (p : SInf F (Fin n × Fin d) →ₗ[ℂ] Pi) (N : Submodule ℂ Pi)
    (hlie : ∀ γ ∈ Lines σ W, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ → p f ∈ N → p f₁ ∈ N)
    {k : UA σ W.J} (hk : k ∈ KInf σ W B.emb) {f : SInf F (Fin n × Fin d)} (hf : f ∈ M.Pol B.ψ B.emb)
    {f₁ : SInf F (Fin n × Fin d)} (hact1 : Acts (evI F) (om (1, k)) f f₁) (hfN : p f ∈ N) : p f₁ ∈ N := by
  have hAL : ActsLaws := GlobalTheory.RealLift.actsLaws
  have hfr : GlobalTheory.RealLift.FrameEx := GlobalTheory.T.cartanEigen_orthonormalFrame_exists
  have hder : GlobalTheory.RealLift.DerEx := GlobalTheory.T.archHeisenbergDerivatives_exist
  have hvl : GlobalTheory.RealLift.VacLine := GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hder
  have hfe : GlobalTheory.RealLift.FockEx := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives hder
  have hls : GlobalTheory.RealLift.LieScalar := GlobalTheory.T.lieScalar_of_prints_derEx_vacLine hP hder hvl
  have hpr : GlobalTheory.RealLift.PolRange := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws hAL hder hvl
  have hkl : GlobalTheory.RealLift.KLine := GlobalTheory.RealLift.kLine_of_lineEx GlobalTheory.T.unitaryLieElements_generate_oneParamLines
  choose A hA hAθ using fun w => hfr _ _ _ _ _ (hX.sig w) (hX.cartan w)
  choose C hC hCθ using fun w => hfr _ _ _ _ _ (hW.sig w) (hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [GlobalTheory.PolCompact.incM_map_piInf', one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [GlobalTheory.PolCompact.incM_map_piInf']; exact hC w
  have fr : Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := hpr F E σ _ _ _ _ _ _ X W M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (incM F W.J) M.co χX χW om := hw
  obtain ⟨c, hact⟩ := hls F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C Φ _ hb.cm hb.std fr hΦ hwp.1.1
  have hadm := fun g => (hwp.isUSplitting).adm g
  obtain ⟨γ, hγ, Yg, hgen, hKC, hγ1⟩ :=
    hkl F E σ (Fin d) _ _ B.emb (incM F W.J) Complex.I C W.θ hb.cm hC1 hCθ k hk.1 hk.2
  have hloc := GlobalTheory.RealLift.locFin_sumPl _ _ _
    (fun w => GlobalTheory.PolCompact.locFin_second r s r' s' (Yg w) (hKC w) (c w * (Yg w).trace))
  obtain ⟨U, hU, hSA⟩ := GlobalTheory.T.weakExponential_action_on_fockVectors F (Fin n × Fin d) _ Φ _ ((om.comp (MonoidHom.inr _ _)).comp γ) hloc
    (fun t l hl => hadm _ l hl) (fun T => hact γ hγ Yg hgen T)
  rw [← hr] at hf
  obtain ⟨T, rfl⟩ := hf

  set N' : Submodule ℂ (Tens F r s r' s') := N.comap (p ∘ₗ Φ) with hN'
  have hstab : ∀ y ∈ N', sumPl (fun w => fockAct2 r s r' s' (Yg w) + (c w * (Yg w).trace) • 1) y ∈ N' := by
    intro y hy
    have hsd := hact γ hγ Yg hgen y
    have had : ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (Φ y)
        (Φ (sumPl (fun w => fockAct2 r s r' s' (Yg w) + (c w * (Yg w).trace) • 1) y)) :=
      (hAL F (Fin n × Fin d) _ _ (Φ y)).1 _ (fun t => map_zero _) hsd
    have hy' : Φ y ∈ M.Pol B.ψ B.emb := hr ▸ LinearMap.mem_range_self Φ y
    exact hlie γ hγ _ hy' _ had hy
  have hUT : U T ∈ N' := mem_of_isExp hU N' hstab hfN
  have h1 := hSA T
  rw [MonoidHom.comp_apply, hγ1] at h1
  have hA2 : Acts (evI F) (om (1, k)) (Φ T) (Φ (U T)) :=
    (hAL F (Fin n × Fin d) (Φ T) (Φ (U T)) (Φ (U T))).2.1 _ (map_zero _) h1
  have he : f₁ = Φ (U T) := (hAL F (Fin n × Fin d) (Φ T) f₁ (Φ (U T))).2.2.2.1 _ hact1 hA2
  rw [he]
  exact hUT

theorem lieStable_kStable : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ N : Submodule ℂ R.Pi,
      (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ Γ.W, ∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ →
        R.p f ∈ N → R.p f₁ ∈ N) →
      ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ Γ.W Bs.emb, ∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (1, k)) f f₁ → R.p f ∈ N → R.p f₁ ∈ N := by
  intro hP F E _ _ _ _ _ σ a a' Bs Γ Xc om om' R Rf h N hlie k hk f hf f₁ hact hN
  exact kStable_of_lieStable hP h.triple.base h.triple.geo.hV h.triple.geo.hW h.triple.weil R.p N hlie hk hf hact hN

end GlobalTheory.KStableLie

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsGaussianIdentity
section
open NumberField IsDedekindDomain
open scoped Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.HoweNonsplitKerSmall

theorem det_ne_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]; ext i j; simp [A', Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.map_apply]
  have h2 : (A'ᵀ * M * A'.map star).det ≠ 0 := by
    rw [h1, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    simp [Matrix.det_neg]
  intro h0
  apply h2
  rw [Matrix.det_mul, Matrix.det_mul, h0]; simp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem det_ne_of_sig {n r s : ℕ} (B : Base F E) (J : Matrix (Fin n) (Fin n) E) (c : ℂ)
    (h : ∀ w, HasSig (c • J.map (B.emb w).1) r s) : J.det ≠ 0 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have := det_ne_of_hasSig (h w)
  intro h0; apply this
  have e := RingHom.map_det (B.emb w).1 J
  rw [RingHom.mapMatrix_apply] at e
  rw [Matrix.det_smul, ← e, h0, map_zero, mul_zero]

theorem isHecke_div {χ₁ χ₂ : Chr F E} (h₁ : IsHecke F E χ₁) (h₂ : IsHecke F E χ₂) : IsHecke F E (χ₁ / χ₂) := by
  refine ⟨?_, fun x => ?_⟩
  · show Continuous fun x => χ₁ x / χ₂ x
    exact h₁.1.div' h₂.1
  · rw [MonoidHom.div_apply, h₁.2 x, h₂.2 x, div_one]

theorem resEtaPow_div {K : Subgroup (AF F)ˣ} {χ₁ χ₂ : Chr F E} {n₁ n₂ n : ℕ} (h₁ : ResEtaPow K χ₁ n₁)
    (h₂ : ResEtaPow K χ₂ n₂) (he : Even (n₁ + n₂)) (hn : Even n) : ResEtaPow K (χ₁ / χ₂) n := by
  intro x
  have e₁ := h₁ x
  have e₂ := h₂ x
  rw [MonoidHom.div_apply, Circle.coe_div, e₁, e₂, hn.neg_one_pow]
  split_ifs
  · simp
  · rcases Nat.even_or_odd n₁ with h | h
    · have h' : Even n₂ := (Nat.even_add.mp he).mp h
      rw [h.neg_one_pow, h'.neg_one_pow]; simp
    · have h' : Odd n₂ := by
        rcases Nat.even_or_odd n₂ with h'' | h''
        · exact absurd ((Nat.even_add.mp he).mpr h'') (Nat.not_even_iff_odd.mpr h)
        · exact h''
      rw [h.neg_one_pow, h'.neg_one_pow]; simp

theorem isPair_second {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (h : IsTriple B G X om om') :
    GlobalTheory.ThK.IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV', h.geo.hW, h.geo.hM', h.chars.heckeα, isHecke_div h.chars.heckeα h.chars.heckeβ, h.chars.resα,
    resEtaPow_div h.chars.resα h.chars.resβ (by rw [add_comm]; exact h.geo.even) h.geo.even, h.weil'⟩

theorem howe_nonsplit_ker_small : GlobalTheory.Published.HoweDualityFinite →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, IsEmpty (E →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) →
      (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ ((Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ)),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSub om' v (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ), GlobalTheory.Published.ThetaSub om' v N →
        N ≠ GlobalTheory.WeilM.SB _ → ∀ φ ∈ N, Rf.p' v φ = 0 := by
  intro hHD F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM v hv
  have hT := hM.triple
  have P := isPair_second hT
  obtain ⟨hbdd, hsum⟩ := hHD F E σ P.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' P.base.std
    P.herm.herm (det_ne_of_sig Bs G.V'.J 1 (fun w => by rw [one_smul]; exact P.herm.sig w)) P.skew.skew
    (det_ne_of_sig Bs G.W.J _ P.skew.sig) P.resX P.resW P.hX P.hW P.weil v hv
  refine ⟨hbdd, ?_⟩
  intro N hN hNe φ hφ
  have hex : ∀ h ∈ UAt σ G.W (evFin F v), ∀ ψ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∃ ψ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (om' (1, h)) ψ ψ₁ :=
    GlobalTheory.T.weilRepresentation_localAtFinitePlace_unitaryGroupW F E σ Bs a a' G Xc om om' hT v
  set K : Submodule ℂ ((Fin a' × Fin (a + a') → Fv F v) → ℂ) :=
    LinearMap.ker (Rf.p' v) ⊓ SB (Fin a' × Fin (a + a') → Fv F v) with hKdef
  have haugSB : augAt om' v ≤ SB (Fin a' × Fin (a + a') → Fv F v) := by
    refine Submodule.span_le.2 ?_
    rintro z ⟨g, -, ψ, hψ, ψ₁, hψ₁, -, rfl⟩
    exact sub_mem hψ₁ hψ
  have hK : GlobalTheory.Published.ThetaSub om' v K := by
    refine ⟨le_inf (hM.fin.inv' v) haugSB, inf_le_right, ?_⟩
    intro h hh ψ hψ ψ₁ hψ₁ hact
    have hψ' := Submodule.mem_inf.1 hψ
    have h0 : Acts (evFin F v) (om (1, h)) (0 : (Fin a × Fin (a + a') → Fv F v) → ℂ) 0 := by
      intro r _
      have e : tens (evFin F v) (0 : (Fin a × Fin (a + a') → Fv F v) → ℂ) r = 0 := by
        funext x; simp [tens]
      rw [e, map_zero]
    have hp := hM.fin.equiv v h hh 0 (zero_mem _) ψ hψ'.2 0 (zero_mem _) ψ₁ hψ₁ h0 hact
      (by rw [map_zero]; exact (LinearMap.mem_ker.1 hψ'.1).symm)
    rw [map_zero] at hp
    exact Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 hp.symm, hψ₁⟩
  have hKne : K ≠ SB (Fin a' × Fin (a + a') → Fv F v) := by
    intro hKe
    have hbot : (SB (Fin a' × Fin (a + a') → Fv F v)).map (Rf.p' v) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      rintro _ ⟨ψ, hψ, rfl⟩
      rw [← hKe] at hψ
      exact LinearMap.mem_ker.1 (Submodule.mem_inf.1 hψ).1
    rw [hM.fin.onto' v] at hbot
    haveI := hM.fin.nontriv v
    exact top_ne_bot hbot
  have hNK : N ⊔ K ≠ SB (Fin a' × Fin (a + a') → Fv F v) := hsum N K hN hK hNe hKne
  rcases hM.fin.irred v (N.map (Rf.p' v)) (by
    intro h hh ψ hψ ψ₁ hψ₁ hact hpm
    obtain ⟨n, hn, hpn⟩ := Submodule.mem_map.1 hpm
    have hnSB : n ∈ SB (Fin a' × Fin (a + a') → Fv F v) := hN.2.1 hn
    obtain ⟨n₁, hn₁, hactn⟩ := hex h hh n hnSB
    have hn₁N : n₁ ∈ N := hN.2.2 h hh n hn n₁ hn₁ hactn
    rw [hM.fin.equiv v h hh ψ hψ n hnSB ψ₁ hψ₁ n₁ hn₁ hact hactn hpn.symm]
    exact Submodule.mem_map_of_mem hn₁N) with h0 | htop
  · have hmem : Rf.p' v φ ∈ N.map (Rf.p' v) := Submodule.mem_map_of_mem hφ
    rw [h0] at hmem
    exact (Submodule.mem_bot ℂ).1 hmem
  · exfalso
    apply hNK
    refine le_antisymm (sup_le hN.2.1 inf_le_right) ?_
    intro ψ hψ
    have hm : Rf.p' v ψ ∈ N.map (Rf.p' v) := by rw [htop]; exact Submodule.mem_top
    obtain ⟨n, hn, hpn⟩ := Submodule.mem_map.1 hm
    have hk : ψ - n ∈ K :=
      Submodule.mem_inf.2 ⟨LinearMap.mem_ker.2 (by rw [map_sub, hpn, sub_self]), sub_mem hψ (hN.2.1 hn)⟩
    have := Submodule.add_mem_sup hn hk
    rwa [add_sub_cancel] at this

end GlobalTheory.HoweNonsplitKerSmall

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedCoordinateSupportIntegralAtLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid

noncomputable section

set_option synthInstance.maxHeartbeats 160000

namespace GlobalTheory.MixSupport

open GlobalTheory.CondBound

theorem annih_den (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (U : AddSubgroup (AE D))
    (hU : IsOpen (U : Set (AE D))) : ∃ N : ℕ, 0 < N ∧ ∀ x : AE D,
      (∀ a ∈ U, infPart D a = 0 → ψ (Algebra.trace (AF D.host.F) (AE D) (x * a)) = 1) → N • finPart D x ∈ intAE D := by
  have hΛ := GlobalTheory.PlaceModel.isSelfDualC_latFrame (line D)
  obtain ⟨M, hM, hden⟩ := den_latL D
  obtain ⟨K0, hK0c, mem0⟩ := exists_compact_fin D M hM
  have memL : ∀ u ∈ latL D, u (o D) (o D) ∈ K0 := fun u hu => mem0 _ (infPart_latL D hu) (hden u hu)
  let c0 : AE D := incA D D.host.xi0 * incA D ((line D).gram⁻¹ (o D) (o D)) * incA D ((line D).gram (o D) (o D))
  obtain ⟨n, hn⟩ := exists_small D _ (isCompact_mul_conj D c0 hK0c) U hU
  let r : AE D := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 ((n.factorial : ℕ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F))
  refine ⟨M * n.factorial, Nat.mul_pos hM (Nat.factorial_pos n), fun x hx => ?_⟩
  let u : WO (line D) (line D) := Matrix.of fun _ _ => x * r
  have hu0 : u.map (infPart D) = 0 := by
    ext i j
    show infPart D (x * r) = 0
    rw [RingHom.map_mul, infPart_r, mul_zero]
  have huL : u ∈ latL D := by
    refine ((GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ (line D) (line D) _ _ hψ hΛ hΛ).1 u hu0).2 fun u' hu' => ?_
    have ha : r * (c0 * cA D (u' (o D) (o D))) ∈ U := hn _ ⟨_, memL u' hu', rfl⟩
    have hai : infPart D (r * (c0 * cA D (u' (o D) (o D)))) = 0 := by
      rw [RingHom.map_mul, infPart_r, zero_mul]
    have h := hx _ ha hai
    rw [symplO, hO_line]
    convert h using 3
    show _ = x * _
    simp only [c0, u, Matrix.of_apply]
    ring
  have h := hden u huL
  have e : finPart D (u (o D) (o D)) = n.factorial • finPart D x := by
    show finPart D (x * r) = _
    rw [RingHom.map_mul, finPart_r, map_natCast, map_natCast, nsmul_eq_mul, mul_comm]
  rw [e, ← mul_nsmul'] at h
  exact h

theorem mul_eq_zero_of_parts {D : D7} (z c : AE D) (hz : finPart D z = 0) (hc : infPart D c = 0) : z * c = 0 := by
  obtain ⟨e, he, -, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  apply e.injective
  refine Prod.ext ?_ ?_
  · rw [(he _).1, (he _).1]
    show infPart D (z * c) = infPart D 0
    rw [map_mul, hc, mul_zero, map_zero]
  · rw [(he _).2, (he _).2]
    show finPart D (z * c) = finPart D 0
    rw [map_mul, hz, zero_mul, map_zero]

theorem mat_den {D : D7} {m : ℕ} (A : Matrix (Fin m) (Fin m) D.host.E) :
    ∃ d : ℕ, 0 < d ∧ ∀ i j, IsIntegral ℤ ((d : D.host.E) * A i j) := by
  choose n hn hint using fun p : Fin m × Fin m => GlobalTheory.IwaPlace.SDBound.exists_nat_mul_isIntegral (D := D) (A p.1 p.2)
  refine ⟨∏ p, n p, Finset.prod_pos fun p _ => hn p, fun i j => ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (i, j)), Nat.cast_mul, mul_comm ((n (i, j) : ℕ) : D.host.E), mul_assoc]
  have hc : IsIntegral ℤ (((∏ p ∈ Finset.univ.erase (i, j), n p : ℕ) : D.host.E)) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := ((∏ p ∈ Finset.univ.erase (i, j), n p : ℕ) : ℤ)))
  exact hc.mul (hint (i, j))

set_option maxHeartbeats 2000000 in
open GlobalTheory.MixModel in

theorem mixS_support_integral : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (V X S₀ : HSp D) (r : ℕ) (d : GlobalTheory.MixModel.HypDec V S₀ r) (μ' : Measure (Mx D X.rank r))
    (𝓕' : Set (Mx D X.rank r)), IsCovolOne (GlobalTheory.MixModel.ratMx D X.rank r) μ' 𝓕' →
    ∀ (K₀ : Set (WO V X)), K₀ ∈ nhds (0 : WO V X) → IsCompact K₀ →
    ∃ M : ℕ, 0 < M ∧ ∀ n : ℕ, 0 < n → ∀ Ψ : WO V X → ℂ, IsThetaFunO ψ V X Ψ →
      (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ V X (n • u) Ψ = Ψ) →
      ∀ (ξ : Matrix (Fin X.rank) (Fin r) D.host.E) (x : Mx D X.rank r),
        x.map (finPart D) = (ξ.map (incA D) : Mx D X.rank r).map (finPart D) → d.mixS X ψ μ' 𝓕' Ψ x 0 ≠ 0 →
        ∀ i j, IsIntegral ℤ (((M * n : ℕ) : D.host.E) * ξ i j) := by
  intro D ψ hψ V X S₀ r d μ' 𝓕' hμ K₀ hK₀ _
  obtain ⟨U, hUo, hU⟩ := GlobalTheory.MixSumBound.finite_points_in_nhds D X.rank V.rank K₀ hK₀
  let g : Fin X.rank → Fin r → (AE D →+ Mx D X.rank r) := fun i j =>
    { toFun := fun c => Matrix.single i j (cA D c)
      map_zero' := by simp
      map_add' := fun a b => by simp [Matrix.single_add] }
  have hg : ∀ i j, Continuous (g i j) := fun i j => by
    show Continuous fun c => Matrix.single i j (cA D c)
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Matrix.single_apply]
    split_ifs
    · exact GlobalTheory.AnnihBox.continuous_cA'
    · exact continuous_const
  have hf : ∀ i j, Continuous ((d.extY X).comp (g i j)) := fun i j => by
    show Continuous fun c => d.extY X (g i j c)
    simp only [HypDec.extY_apply]
    exact (hg i j).matrix_mul continuous_const
  have hg0 : ∀ i j c, infPart D c = 0 → (g i j c).map (infPart D) = 0 := fun i j c hc0 => by
    ext a b
    show infPart D (Matrix.single i j (cA D c) a b) = 0
    simp only [Matrix.single_apply]
    split_ifs
    · exact GlobalTheory.AnnihBox.infPart_cA' c hc0
    · exact map_zero _
  let U' : AddSubgroup (AE D) := ⨅ i, ⨅ j, U.comap ((d.extY X).comp (g i j))
  have hU'o : IsOpen (U' : Set (AE D)) := by
    have e : (U' : Set (AE D)) = ⋂ i, ⋂ j, ((d.extY X).comp (g i j)) ⁻¹' (U : Set (WO V X)) := by
      ext c; simp [U', AddSubgroup.mem_iInf]
    rw [e]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hUo.preimage (hf i j)
  obtain ⟨N, hN, hNden⟩ := annih_den D ψ hψ U' hU'o
  obtain ⟨M₂, hM₂, hM₂i⟩ := mat_den (D := D) (D.host.xi0⁻¹ • X.gram⁻¹)
  refine ⟨M₂ * N, Nat.mul_pos hM₂ hN, fun n hn Ψ hΨ hfix ξ x hx hne i j => ?_⟩
  let v : GlobalTheory.Unf.VolM D X.rank r := ⟨μ', 𝓕', hμ⟩
  have hmix := (GlobalTheory.HeisMixSource.heis_mixS D ψ hψ V S₀ X r d v Ψ hΨ).2.1
  have hxr : (x - rat ξ).map (finPart D) = 0 := by
    rw [Matrix.map_sub _ (map_sub (finPart D))]
    exact sub_eq_zero.2 hx
  have key : ∀ k l, IsIntegral ℤ ((N : D.host.E) * ((n : D.host.E) * (D.host.xi0 * (X.gram * ξ) k l))) := by
    intro k l
    have hann : ∀ c ∈ U', infPart D c = 0 → ψ (Algebra.trace (AF D.host.F) (AE D)
        (incA D ((n : D.host.E) * (D.host.xi0 * (X.gram * ξ) k l)) * c)) = 1 := by
      intro c hc hc0
      have hcU : d.extY X (g k l c) ∈ U := AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 hc k) l
      have hfin : (d.extY X (g k l c)).map (infPart D) = 0 := by
        rw [HypDec.extY_apply, Matrix.map_mul, hg0 k l c hc0, Matrix.zero_mul]
      have hfx := hfix _ (hU _ hcU hfin) hfin
      have h2 := congrFun (hmix x (n • g k l c)) 0
      rw [map_nsmul, hfx, Pi.smul_apply, smul_eq_mul] at h2
      have h3 : ψ (symplO V X (d.extX X x) (n • d.extY X (g k l c))) = 1 := by
        have hne' : d.mixS X ψ v.μ v.𝓕 Ψ x 0 ≠ 0 := hne
        exact mul_right_cancel₀ hne' (h2.symm.trans (one_mul _).symm)
      rw [← map_nsmul (d.extY X), ← map_nsmul (g k l), show g k l (n • c) = Matrix.single k l (cA D (n • c)) from rfl,
        GlobalTheory.AnnihBox.symplO_extX_extY_single] at h3
      rw [← h3]
      congr 2
      have hxc : (gA X * x) k l * c = incA D ((X.gram * ξ) k l) * c := by
        rw [← sub_eq_zero, ← sub_mul]
        refine mul_eq_zero_of_parts _ _ ?_ hc0
        have e1 : incA D ((X.gram * ξ) k l) = (gA X * rat ξ) k l := by
          rw [gA, ← rat_mul]; rfl
        rw [e1, ← Matrix.sub_apply, ← Matrix.mul_sub]
        exact congrFun (congrFun (map_mul_eq_zero_right (finPart D) (gA X) hxr) k) l
      calc incA D ((n : D.host.E) * (D.host.xi0 * (X.gram * ξ) k l)) * c
          = (n : AE D) * (incA D D.host.xi0 * (incA D ((X.gram * ξ) k l) * c)) := by
            simp only [map_mul, map_natCast]; ring
        _ = (n : AE D) * (incA D D.host.xi0 * ((gA X * x) k l * c)) := by rw [hxc]
        _ = incA D D.host.xi0 * (gA X * x) k l * (n • c) := by rw [nsmul_eq_mul]; ring
    have h := hNden _ hann
    have e : finPart D (incA D ((N : D.host.E) * ((n : D.host.E) * (D.host.xi0 * (X.gram * ξ) k l)))) =
        N • finPart D (incA D ((n : D.host.E) * (D.host.xi0 * (X.gram * ξ) k l))) := by
      rw [map_mul (incA D), map_mul (finPart D), map_natCast, map_natCast, nsmul_eq_mul]
    rw [← e] at h
    obtain ⟨y, hy⟩ := GlobalTheory.FinalJoin.CondTest.integral_of_mem_intAE h
    have e2 : ((N : D.host.E) * ((n : D.host.E) * (D.host.xi0 * (X.gram * ξ) k l))) = (y : D.host.E) := hy.symm
    rw [e2]
    convert NumberField.RingOfIntegers.isIntegral_coe y
  have hξ : ξ = X.gram⁻¹ * (X.gram * ξ) := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (gram_isUnit_det X), Matrix.one_mul]
  have e : (((M₂ * N * n : ℕ)) : D.host.E) * ξ i j = ∑ k, ((M₂ : D.host.E) * (D.host.xi0⁻¹ • X.gram⁻¹) i k) *
      ((N : D.host.E) * ((n : D.host.E) * (D.host.xi0 * (X.gram * ξ) k j))) := by
    conv_lhs => rw [hξ]
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
    simp only [Matrix.smul_apply, smul_eq_mul]
    push_cast
    field_simp
  rw [e]
  exact IsIntegral.sum _ fun k _ => (hM₂i i k).mul (key k j)

end GlobalTheory.MixSupport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitThetaGridIsAdmissibleFlipTensorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitThetaGrid_isAdmissible_flipTensor : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ), IsUnif ϖ → HasConductor ψ 1 → 1 ≤ e →
    ∀ (St : Γ.PiLocalization₂) (x : ℕ × ℕ), CondLE ϖ e (Γ.nu x.1 x.2) → PassesThrough x.1 x.2 St.path →
    (∀ X, IsOpen (St.level X : Set (GL (Fin (Γ.rank X)) k)) ∧ St.level X ≤ KO k _) →
    St.IsAdmissible .one ϖ e → (St.flip .one ψ ϖ e x).IsAdmissible .one ϖ e := by
  first | exact @GlobalTheory.FlipAdm.isAdmissible_flip | exact GlobalTheory.FlipAdm.isAdmissible_flip | (intros; apply GlobalTheory.FlipAdm.isAdmissible_flip <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftVerticalCuspidalSumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_vertical_cuspidal_sum : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t j, j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.Xp j).V (G.Xp (j + 1)).V Φ →
    ∀ (n : ℕ) (F : Fin n → (G.Xp j).Cusp R.θ) (w : Fin n → SmT (G.Xp j).M),
    (∀ h, IntegrableOn (fun g => thetaKO (G.col t j).ω g h Φ * (∑ i, (F i).1 (w i)) g) (G.measX j).fd (G.measX j).ν) →
    ∃ (k : ℕ) (F' : Fin k → (G.Xp (j + 1)).Cusp R.θ) (z : Fin k → SmT (G.Xp (j + 1)).M),
      (fun h => ∫ g in (G.measX j).fd, thetaKO (G.col t j).ω g h Φ * (∑ i, (F i).1 (w i)) g ∂(G.measX j).ν) = ∑ i, (F' i).1 (z i) := by
  first | exact @GlobalTheory.ColFockRed.lift_finSum_smooth | exact GlobalTheory.ColFockRed.lift_finSum_smooth | (intros; apply GlobalTheory.ColFockRed.lift_finSum_smooth <;> assumption)
end

