import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0312
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0321
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0325
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0012
import Formalism.LocalToGlobal.InertKernelTheory.GenusOneModelExistsLattice
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0007
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0005
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0027
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThreeLeSplitAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0311
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSpherical
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0374
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0122
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0102
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0316
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0326
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0327
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValMulVecLe
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0191
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0314

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointsEqualEigenMatch
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EigAgree

theorem cls_eq_of_locV_eq (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (i : D.nd.Loc) (Q Q' : D.naut.AV i)
    (sp : SplitPlace D.host.E) (σ σ' : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.nV) (sp.w.adicCompletion D.host.E)))
    (hσ : IsLocS (P.H.av.S i Q) sp σ) (hσ' : IsLocS (P.H.av.S i Q') sp σ')
    (he : D.naut.locV i Q sp.w = D.naut.locV i Q' sp.w) :
    GlobalTheory.LocLanglands.cls σ = GlobalTheory.LocLanglands.cls σ' := by
  have h3 := P.au (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (P.H.av.rep i Q) sp σ hσ
  have h3' := P.au (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 (P.H.av.rep i Q') sp σ' hσ'
  rw [← P.H.emb i Q, ← D.nbc.embAV_loc i Q sp.w] at h3
  rw [← P.H.emb i Q', ← D.nbc.embAV_loc i Q' sp.w] at h3'
  rw [he] at h3
  obtain ⟨a, ha, ε, -, hlaws⟩ := GlobalTheory.CuspRep.ParLaws.isRec_locRec hL (D.nd.plOm.2 sp.w)
  exact hlaws.bij.1 (h3.symm.trans h3')

end GlobalTheory.EigAgree

theorem GlobalTheory.EigAgree.cast_ne_zero {D : D7} {μ : D.what₂.Tup} {a b : ℕ} (h : a = b) (f : D.what₂.Mt μ a) (hf : f ≠ 0) :
    (h ▸ f : D.what₂.Mt μ b) ≠ 0 := by
  subst h
  exact hf

theorem GlobalTheory.EigAgree.eig_agree : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.adm7 D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ (x : D.nd.X i) (Q Q' : D.naut.AV i), D.naut.ptV i Q = some x → D.naut.ptV i Q' = some x → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (Pp.under (𝓞 D.host.F)) → Pp ∉ D.nd.S i → Pp ∉ D.nd.Q i → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) Pp d → ∀ f₁ f₂ : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f₁ : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q → (hj ▸ f₂ : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ D.naut.typeV i Q' → f₁ ≠ 0 → f₂ ≠ 0 → ∀ c₁ c₂ : ℂ, (∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f₁ (g * γ) = c₁ • X.fn hμ j f₁ g) → (∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.fn hμ j f₂ (g * γ) = c₂ • X.fn hμ j f₂ g) → c₁ = c₂ := by
  intro hAF hL D P X hA h41 h7 htie i hμ j hj x Q Q' hQ hQ' Pp hG hS hPS hPQ d hd f₁ f₂ hf₁ hf₂ h0₁ h0₂ c₁ c₂ e1 e2
  have hsplit : IsSplitPl D.host Pp := GlobalTheory.OffBad.isSplitPl_of_isSplit D Pp hS
  have hloc : D.naut.locV i Q Pp = D.naut.locV i Q' Pp :=
    (((h41 i).2.1 Q Q' (by rw [hQ]; exact Option.some_ne_none x) (hQ.trans hQ'.symm)).2 Pp hPS hPQ).1 hsplit
  obtain ⟨sp, hspw, hJ⟩ := GlobalTheory.OffBad.offbad hAF hL D P X hA h41 h7 htie i Pp hG hS
  subst hspw
  obtain ⟨Ds, hD1, hD2, hD3, hDt⟩ := GlobalTheory.T.split_place_hecke_satake hAF hL D P X hA h41 h7 htie i hμ j hj sp hG hS hJ d hd
  have E1 := hDt f₁ c₁ e1
  have E2 := hDt f₂ c₂ e2
  have m1 : (P.M.loc i).real (hj ▸ f₁) ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) := by
    have := P.H.av.typeV i Q ▸ hf₁
    exact this
  have m2 : (P.M.loc i).real (hj ▸ f₂) ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q') := by
    have := P.H.av.typeV i Q' ▸ hf₂
    exact this
  have t1 : (P.M.loc i).real (hj ▸ f₁) ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ :=
    (P.M.loc i).real_range ▸ LinearMap.mem_range_self _ _
  have t2 : (P.M.loc i).real (hj ▸ f₂) ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ :=
    (P.M.loc i).real_range ▸ LinearMap.mem_range_self _ _
  have n1 : (P.M.loc i).real (hj ▸ f₁) ≠ 0 := fun h =>
    GlobalTheory.EigAgree.cast_ne_zero hj f₁ h0₁ ((P.M.loc i).real_inj (h.trans (map_zero _).symm))
  have n2 : (P.M.loc i).real (hj ▸ f₂) ≠ 0 := fun h =>
    GlobalTheory.EigAgree.cast_ne_zero hj f₂ h0₂ ((P.M.loc i).real_inj (h.trans (map_zero _).symm))
  exact GlobalTheory.T.double_coset_support_at_split hAF hL D P i Q Q' sp hJ Ds hD1 hD2 hD3
    (fun σ σ' h h' => GlobalTheory.EigAgree.cls_eq_of_locV_eq hL D P i Q Q' sp σ σ' h h' hloc) _ m1 t1 n1 _ m2 t2 n2 c₁ c₂ E1 E2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowAtOfStdTie
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Pdv

theorem rowAt_of_stdTie : Formalism.L2.KerInert.AlgTAll → Formalism.L2.KerInert.GenusOneModelExistsLattice → Formalism.L2.KerInert.Rep.CurveDict → Formalism.L2.KerInert.IntInert → ∀ {Bd : BdT} (Q : V4.Slot) (Lk : LkT Bd) (ker : ∀ (D : D7) (O : Obj D) (c : ℝ), Bd D O c → KerEntTied O.ex), RowE Q Lk (fun _ D O c b => StdTie D O (ker D O c b)) → Row Q Lk (AtAll fun D O c b => GlobalTheory.Pdv.At O.ex (ker D O c b).ent) := by
  intro hA hG hD hI Bd Q Lk ker hE
  choose x0 hx0 using GlobalTheory.ShapeUniform.shape_uniform
  refine ⟨fun κ D O c b => x0 κ.eps ≤ O.L.sc.x ∧ StdTie D O (ker D O c b), ?_, ?_⟩
  · have h1 : RowE Q Lk (fun κ D O _ _ => x0 κ.eps ≤ O.L.sc.x) := by
      unfold RowE EvP
      refine ParEv.of_all fun κ _ => ⟨x0 κ.eps, fun K hk hx β _ c b _ => ?_⟩
      show x0 κ.eps ≤ β.p.L.sc.x
      rw [β.sc]
      exact hx
    exact (h1.and hE).mono fun _ _ _ H => H
  · intro 𝒜 σ s eps Fm hc x hx i
    obtain ⟨κ, hl, _, ht⟩ := s Fm hc
    obtain ⟨_, h0, hst⟩ := ht x hx i
    have hxx : (Fm.L x i).sc.x = x := Fm.L_x x i hx
    have hge : x0 eps ≤ x := by
      have h0' : x0 κ.eps ≤ (Fm.L x i).sc.x := h0
      rw [hl.eps_eq, hxx] at h0'
      exact h0'
    have hsh := hx0 eps Fm x hge hx i
    have hsb : 3 ≤ (Fm.D x i).host.splitBound :=
      (hsh (OrbitPlaces.ofKer (nuRowOK (Fm.D x i)) (ker _ _ _ (σ Fm hc x hx i)).ent (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0))).2.2
    exact GlobalTheory.T.kernelDatumConditions_at_standardKernelComparison hA hG hD hI (Fm.D x i) (objAt Fm x hx i) (ker _ _ _ (σ Fm hc x hx i)) hst hsb
      Fm.fixed.2.1.ge Fm.fixed.2.2.1.ge (fun Ee => ⟨(hsh Ee).1, (hsh Ee).2.1⟩)

end GlobalTheory.Pdv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardElementSplitPlaceLabel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

namespace GlobalTheory.StdEltLabel

set_option maxHeartbeats 4000000 in
theorem std_elt_label : ∀ {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : TH.HSp D} {n : ℕ} (Ps : Formalism.IndefR.principalLevelFrame.RowPsi V n), GlobalTheory.NJoin.StdFrame hF Ps → V.rank = n → ∀ (sp : SplitPlace D.host.E) (ϖ : (sp.v).adicCompletion (maximalRealSubfield D.host.E)), Formalism.AUTREP.IsUnif D.host.E sp.v ϖ → ∀ k ≤ n, ∃ x₀ ∈ Formalism.AUTREP.tSet D.host.E n sp ϖ k, ∃ (e f : Formalism.L2.Theta.AE D) (ϖ' : 𝓞 D.host.E), Formalism.IndefR.Mult.IsPrimeIdem sp.w e f ∧ ϖ' ∈ sp.w.asIdeal ∧ ϖ' ∉ sp.w.asIdeal ^ 2 ∧ Formalism.IndefR.Mult.SuppF V f (Ps.ψ x₀) ∧ Formalism.IndefR.Mult.DivAt V e (ϖ' : D.host.E) (List.replicate k 1 ++ List.replicate (n - k) 0) (Ps.ψ x₀) := by
  intro D hF V n Ps hS hn sp ϖ hϖ k hk
  subst hn
  classical
  obtain ⟨⟨β, β', h1, h2, hm⟩, hK⟩ := id hS
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    have := hϖ
    rw [Formalism.AUTREP.IsUnif, h0, map_zero] at this
    exact WithZero.zero_ne_coe this
  let g0 : GL (Fin V.rank) (sp.v.adicCompletion (maximalRealSubfield D.host.E)) :=
    ⟨Formalism.UG.diagJ V.rank ϖ k, Matrix.diagonal (fun i => if (i : ℕ) < k then ϖ⁻¹ else 1),
      by
        rw [Formalism.UG.diagJ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1; funext i; split_ifs <;> simp [hϖ0],
      by
        rw [Formalism.UG.diagJ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1; funext i; split_ifs <;> simp [hϖ0]⟩
  obtain ⟨emb, hembT, hembL⟩ := GlobalTheory.SplitEmb.exists_hom_trivOutside_loc D.host.E V.rank sp
  have hx₀ : emb g0 ∈ Formalism.AUTREP.tSet D.host.E V.rank sp ϖ k :=
    ⟨hembT g0, 1, one_mem _, 1, one_mem _, by rw [hembL]; simp [g0]⟩
  obtain ⟨p, c, hpl, -, -, hπ⟩ := GlobalTheory.T.exists_splitLocalPlaceData_at_splitPlace D sp hF
  have hidem : Formalism.L2.NTheta.IsIdemAt p.e sp.w := ⟨p.split, hpl.2.2⟩
  have hprime : Formalism.IndefR.Mult.IsPrimeIdem sp.w p.e (p.e + Formalism.L2.Theta.cA D p.e) := Or.inl ⟨hidem, rfl⟩
  obtain ⟨y, hy1, hy2, hyu⟩ := GlobalTheory.T.exists_realSubfield_uniformizer_at_splitPlace sp
  refine ⟨emb g0, hx₀, p.e, p.e + Formalism.L2.Theta.cA D p.e, y, hprime, hy1, hy2,
    (GlobalTheory.LabelTransport.suppF_iff_trivOutside D sp hF V V.rank Ps hS _ _ hprime (emb g0)).2 (hembT g0), ?_⟩
  obtain ⟨sec, hs, hO', hO, hinc⟩ := GlobalTheory.T.exists_integralSection_splitPlace_componentMap D sp hF
  obtain ⟨hε, hker⟩ := GlobalTheory.T.splitPlaceIdempotent_component_one_determines_part D sp hF p c hπ
  let φ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E →+* sp.v.adicCompletion (maximalRealSubfield D.host.E) :=
    sp.proj.comp (GlobalTheory.NJoin.tensCast hF).toRingHom
  have hφ : ∀ x, φ x = sp.proj (GlobalTheory.NJoin.tensCast hF x) := fun x => rfl
  have he : p.e * p.e = p.e := p.split.1
  obtain ⟨B, b1, b2⟩ := GlobalTheory.SphLabelOps.exists_basis (P := sp.w) V he (GlobalTheory.SphLabelOps.tie_of_isPrimeIdem hprime)
  have hee : Formalism.L2.Theta.finPart D p.e * Formalism.L2.Theta.finPart D p.e = Formalism.L2.Theta.finPart D p.e := by
    rw [← map_mul, he]
  obtain ⟨C, c1, c2⟩ := (GlobalTheory.LatIntFacts.int_facts V).2.2 _ B hee fun y hy => (b2 y hy).imp fun _ h => h.2
  have mp : ∀ X Y : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E),
      Formalism.L2.Theta.finPart D p.e • (X * Y) = Formalism.L2.Theta.finPart D p.e • (1 : Matrix (Fin V.rank) (Fin V.rank) _) →
        X.map φ * Y.map φ = 1 := by
    intro X Y hXY
    rw [← Matrix.map_mul, ← Matrix.map_one φ (map_zero φ) (map_one φ)]
    refine Matrix.ext fun i j => ?_
    have := congrArg φ (congrFun (congrFun hXY i) j)
    rwa [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_mul, hφ, hε, one_mul,
      one_mul] at this
  have hBC := mp _ _ c1
  have hCB := mp _ _ c2
  have hββ' : β.map φ * β'.map φ = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one φ (map_zero φ) (map_one φ)]
  have hβ'β : β'.map φ * β.map φ = 1 := by
    rw [← Matrix.map_mul, h2, Matrix.map_one φ (map_zero φ) (map_one φ)]
  obtain ⟨N, hNdef⟩ : ∃ N : GL (Fin V.rank) (sp.v.adicCompletion (maximalRealSubfield D.host.E)),
      (N : Matrix (Fin V.rank) (Fin V.rank) _) = β'.map φ * B.map φ :=
    ⟨⟨β'.map φ * B.map φ, C.map φ * β.map φ,
      by rw [Matrix.mul_assoc, ← Matrix.mul_assoc (B.map φ), hBC, Matrix.one_mul, hβ'β],
      by rw [Matrix.mul_assoc, ← Matrix.mul_assoc (β.map φ), hββ', Matrix.one_mul, hCB]⟩, rfl⟩
  have hlat := GlobalTheory.T.standardFrame_conj_GLint_le_selfDualLattice_stabilizer hF Ps sp β β' h1 h2 hm hK (Formalism.L2.Theta.finPart D p.e) sec B hs hO' hO hε b1 b2
  obtain ⟨k₁, hk₁, k₂, hk₂, hkk⟩ := GlobalTheory.T.normaliser_GLint_conj_eq_two_sided_GLint_mul _ sp.v V.rank N (by rw [hNdef]; exact hlat) (Formalism.UG.diagJ V.rank ϖ k)
  obtain ⟨T, hT, hTe⟩ := GlobalTheory.T.diagUniformizerBlock_eq_diagonal_pow_mul_integralGL _ sp.v V.rank k ϖ (sp.i (y : D.host.E)) hϖ hyu
  rw [GlobalTheory.DivDual.divAt_iff]
  refine ⟨by simp [hk], ?_⟩
  have hk₂' : T * k₂ ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov (maximalRealSubfield D.host.E) sp.v) := mul_mem hT hk₂
  refine GlobalTheory.SphLabelOps.dv_of_cartan (OK := Formalism.UG.Ov (maximalRealSubfield D.host.E) sp.v) φ sec hs hε hker
    (fun x hx => hO x hx) (fun t ht => hO' t ht) b1 b2
    (Formalism.UG.P.cartan_entries_of_mem _ _ hk₁) (Formalism.UG.P.cartan_entries_of_mem _ _ (inv_mem hk₁))
    (Formalism.UG.P.cartan_entries_of_mem _ _ hk₂') (Formalism.UG.P.cartan_entries_of_mem _ _ (inv_mem hk₂')) ?_
  have hdiag : (Matrix.diagonal fun i : Fin V.rank => φ (Formalism.L2.Theta.finPart D (Formalism.L2.Theta.incA D
      ((y : D.host.E) ^ ((List.replicate k (1 : ℤ) ++ List.replicate (V.rank - k) 0).getD i.1 0))))) =
      Matrix.diagonal (fun i : Fin V.rank => sp.i (y : D.host.E) ^
        ((List.replicate k (1 : ℤ) ++ List.replicate (V.rank - k) 0).getD i.1 0)) := by
    congr 1; funext i; rw [hφ, hinc, map_zpow₀]
  have hA : (Formalism.MainNotions.StandardLattice.finMat D.sp.cm.sig V.gram (Ps.ψ (emb g0))).map φ =
      β.map φ * Formalism.UG.diagJ V.rank ϖ k * β'.map φ := by
    rw [hm, Matrix.map_mul, Matrix.map_mul]
    congr 2
    have e2 : ((emb g0).1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)).map sp.proj =
        Formalism.UG.diagJ V.rank ϖ k := congrArg Units.val (hembL g0)
    rw [← e2, Matrix.map_map]
    congr 1
    funext x
    simp [φ]
  have hBN : B.map φ = β.map φ * (N : Matrix (Fin V.rank) (Fin V.rank) _) := by
    rw [hNdef, ← Matrix.mul_assoc, hββ', Matrix.one_mul]
  have hNN : (N : Matrix (Fin V.rank) (Fin V.rank) _) *
      (N⁻¹).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hdiag, hA, hBN]
  calc β.map φ * Formalism.UG.diagJ V.rank ϖ k * β'.map φ * (β.map φ * (N : Matrix (Fin V.rank) (Fin V.rank) _))
      = β.map φ * Formalism.UG.diagJ V.rank ϖ k * (N : Matrix (Fin V.rank) (Fin V.rank) _) := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (β'.map φ), hβ'β, Matrix.one_mul]
    _ = β.map φ * ((N : Matrix (Fin V.rank) (Fin V.rank) _) *
          ((N⁻¹).val *
            Formalism.UG.diagJ V.rank ϖ k * (N : Matrix (Fin V.rank) (Fin V.rank) _))) := by
        have e3 : (N : Matrix (Fin V.rank) (Fin V.rank) _) * ((N⁻¹).val * Formalism.UG.diagJ V.rank ϖ k * (N : Matrix (Fin V.rank) (Fin V.rank) _)) =
            Formalism.UG.diagJ V.rank ϖ k * (N : Matrix (Fin V.rank) (Fin V.rank) _) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hNN, Matrix.one_mul]
        rw [e3, Matrix.mul_assoc]
    _ = _ := by
        rw [hkk, hTe]
        simp only [Units.val_mul, Matrix.mul_assoc]

end GlobalTheory.StdEltLabel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaEigenCompatibilityNinth
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertEigSat

set_option maxHeartbeats 4000000 in

theorem heckeFunI_eigC (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (h41 : Formalism.MainNotions.SumRepresentations.Conclusion41 D)
    (i : D.nd.Loc) (x : D.nd.X i) {w : HeightOneSpectrum (𝓞 D.host.E)} (hns : ¬ Formalism.BasicNotions.IsSplitPl D.host w)
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))} (hov : NG.OverPl w v)
    (Dv : InertDatum D.host.E D.R.nV v w)
    (hfix : ∀ g : D.what₂.Mt (D.nd.mu i) (D.nd.j i), ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {v} κ →
      NG.rt D.host.E D.R.nV κ ((P.M.loc i).real g) = (P.M.loc i).real g)
    (P₀ : D.naut.AV i) (hP₀ : D.naut.ptV i P₀ = some x) (α₀ : Fin (D.R.nV / 2) → ℂ)
    (hα₀ : D.naut.satV i P₀ w = Multiset.map α₀ Finset.univ.val)
    (h0 : Formalism.UG.GU Dv.σw D.R.nV → ℂ) (hh0 : h0 ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw D.R.nV)) :
    ∀ g ∈ eigC D.nd D.naut i x, heckeFunI D.host.E D.R.nV (Umax D.host.E D.R.nV) Dv h0 ((P.M.loc i).real g) =
      Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield D.host.E) v) h0 α₀ • (P.M.loc i).real g := by
  classical
  obtain ⟨C, a, xs, hC⟩ := GlobalTheory.EigInert.heckeFunI_umax_sum Dv h0 hh0
  set c := Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield D.host.E) v) h0 α₀ with hc
  intro g hg
  unfold eigC at hg
  refine Submodule.iSup_induction _ (motive := fun g => heckeFunI D.host.E D.R.nV (Umax D.host.E D.R.nV) Dv h0
    ((P.M.loc i).real g) = c • (P.M.loc i).real g) hg ?_ ?_ ?_
  · intro P' g' hg'
    by_cases hP' : D.naut.ptV i P' = some x
    · rw [iSup_pos (show P' ∈ {P | D.naut.ptV i P = some x} from hP')] at hg'
      obtain ⟨α', hα', hsv'⟩ := GlobalTheory.EigInert.satParam hL D P i P' v w hov hns Dv
      have hub : ubc D.R.nV (D.naut.satV i P' w) = ubc D.R.nV (D.naut.satV i P₀ w) := by
        have h41i := (show Formalism.MainNotions.SumRepresentations.At.Conclusion41 D.nd D.naut i from h41 i).2.1 P' P₀ (by rw [hP']; simp) (by rw [hP', hP₀])
        have hS : w ∉ D.nd.S i := fun hm => hns (D.nd.SQ_split i w (Or.inl hm))
        have hQ : w ∉ D.nd.Q i := fun hm => hns (D.nd.SQ_split i w (Or.inr hm))
        exact (h41i.2 w hS hQ).2 hns
      rw [hsv', hα₀] at hub
      have hW := GlobalTheory.T.satakeTransform_eq_of_unramifiedBaseChange_eq _ Dv.ϖ Dv.σw _ D.R.nV Dv.unram α' _ hub h0 hh0
      rw [hc, ← hW]
      have hmem : (P.M.loc i).real g' ∈ NG.isoTyp (P.H.av.rep i P').ρ (P.H.av.rep i P').S := by
        have h2 := hg'
        rw [P.H.av.typeV] at h2
        exact h2
      exact GlobalTheory.T.isotypicFixedVector_isSatakeEigen_inertPlace _ _ (P.H.av.rep i P') v w hov Dv α' hα' _ hmem (hfix g') h0 hh0
    · rw [iSup_neg (show P' ∉ {P | D.naut.ptV i P = some x} from hP')] at hg'
      rw [(Submodule.mem_bot ℂ).1 hg']
      simp [hC]
  · simp [hC]
  · intro g1 g2 h1 h2
    rw [hC] at h1 h2 ⊢
    simp only [map_add, smul_add, Finset.sum_add_distrib, h1, h2]

open Formalism.IndefR Formalism.IndefR.Links in

theorem real_cast {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    {X : GlobalTheory.NJoin.RealAt D cf nch tp} {M : MtFam D} {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r}
    (A : GlobalTheory.NJoin.Agree X M rep) {μ : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) (k : ℕ)
    (hk : j.1 + 1 = k) (p1 : 1 ≤ k) (p2 : k ≤ D.R.m) :
    ∃ e : (X.R.cV j).W ≃ₗ[ℂ] (M μ k p1 p2).wt.W, ∀ (x : D.what₂.Mt μ (j.1 + 1)) h,
      (M μ k p1 p2).real (hk ▸ x) h = e (X.fn hμ j x ((A.PV j).ψ ((A.a j)⁻¹ * h))) := by
  subst hk
  exact ⟨A.eW μ hμ j, A.real μ hμ j⟩

theorem cast_eq_zero {D : D7} {μ : D.what₂.Tup} {a k : ℕ} (hk : a = k) (x : D.what₂.Mt μ a)
    (h : (hk ▸ x : D.what₂.Mt μ k) = 0) : x = 0 := by
  subst hk
  exact h

open Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Mult Formalism.L2.Theta Formalism.L2.DIV GlobalTheory.Hk3 in
set_option maxHeartbeats 1000000 in

theorem sum_ext {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is)
    {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsSDFrame V β Λ 1)
    {L : LevDat D.host.E ℂ V.rank} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ w ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP w) {f : Bridge.Gf V → c.W}
    (hf : f ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ)
    {d : List ℤ} {R : Finset (GA D V)} (hR : SphOp V w d R) (z : ℂ)
    (he : hkF V w (Finsupp.single d 1) f = z • f) (g : GA D V) :
    ∑ γ ∈ R, c.ext f (g * γ) = z • c.ext f g := by
  obtain ⟨n, hB⟩ := hβ
  rw [one_pow] at hB
  have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := GlobalTheory.DefLiftHecke.one_pow_notMem w 0
  obtain ⟨hk, -⟩ := GlobalTheory.LevOp.level_operators V β Λ 1 (flag1L L) hB w h1 hw
  have h2 := ((GlobalTheory.SphLabelOps.label_operators V w).1 d R hR).2 _
    (GlobalTheory.PRep.rightReg ℂ (GA D V) c.W) (c.ext f) fun k hkk => funext fun g =>
      GlobalTheory.DefLiftHecke.ext_level c hc hf (hk k hkk).1 (hk k hkk).2 g
  have h3 := congrFun h2 g
  have h4 := GlobalTheory.DefLiftHecke.ext_hkF c hc w (Finsupp.single d 1) f g
  rw [he, map_smul, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton,
    Finsupp.single_eq_same, one_smul] at h4
  rw [opOf, Finsupp.sum_single_index (by exact zero_smul _ _), one_smul, Finset.sum_apply, LinearMap.sum_apply,
    Finset.sum_apply] at h3
  exact h3.trans h4.symm

open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.L2.Theta GlobalTheory.Hk3 in
set_option maxHeartbeats 1000000 in

theorem sum_extV {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch}
    (X : GlobalTheory.NJoin.RealAt D cf nch tp) (j : Fin D.R.m) (t : X.T) (h) (hh : IsOpsV X.R j t h)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (hG : Good X.R t w) {d : List ℤ} {R : Finset (GA D (Vc D j))}
    (hR : SphOp (Vc D j) w d R) (y : (X.R.HV j t).H) (c : ℂ) (hy : h w (Finsupp.single d 1) y = c • y) (g) :
    ∑ γ ∈ R, X.R.extV j t y (g * γ) = c • X.R.extV j t y g :=
  have hC := X.given.core
  sum_ext (X.R.cV j) (hC.models.cV j) (hC.lev.βV j) (L := X.R.datVt j t) hG
    ((hC.models.HV j t).2.1.le (LinearMap.mem_range_self _ y)) hR c
    ((hh w hG _ y).symm.trans ((congrArg (X.R.HV j t).e hy).trans (map_smul _ _ _))) g

set_option maxHeartbeats 4000000 in

theorem eig_eq_satU : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.adm7 D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i, ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x → ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ (s : GlobalTheory.DownLift.Sys D), GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) h s y → ∀ w : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.UG.IsInertAt D.host.F D.host.E (w.under (𝓞 D.host.F)) w → ∃ P₀, D.naut.ptV i P₀ = some x ∧ ∃ α₀ : Fin ((Formalism.IndefR.Links.Vc D j).rank / 2) → ℂ, D.naut.satV i P₀ w = Finset.univ.val.map α₀ ∧ ∀ (τ : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (ϖ : w.adicCompletion D.host.E), Formalism.UG.IsUnramInv ϖ τ (Formalism.UG.qV D.host.F (w.under (𝓞 D.host.F))) → GlobalTheory.LFun.IsConjAt D.sp.cm.sig (rfl : w.under (𝓞 D.host.F) = _) τ → ∀ (d : Fin (Formalism.IndefR.Links.Vc D j).rank → ℤ) (t' : Formalism.UG.GU τ (Formalism.IndefR.Links.Vc D j).rank), Antitone d → t'.1.1 = Matrix.diagonal (fun k => ϖ ^ d k) → s w (List.ofFn d) = Formalism.UG.SatU ϖ (Formalism.UG.qV D.host.F (w.under (𝓞 D.host.F))) (Formalism.UG.dosetInd ℂ (Formalism.UG.KU τ (Formalism.IndefR.Links.Vc D j).rank) t') α₀ := by
  intro hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 h hops s hs w hG hin
  classical
  have hn : (Formalism.IndefR.Links.Vc D j).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  have hns : ¬ Formalism.BasicNotions.IsSplitPl D.host w := GlobalTheory.T.not_isSplitPlace_of_inert_over_realSubfield D w hin
  have hf0 : (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ≠ 0 := fun e => hy0 (X.hinj _ _ (by
    rw [hy, cast_eq_zero hj f e, map_zero]
    exact congrArg Subtype.val (map_zero (X.IL.jMt _ hμ j))))
  obtain ⟨P₀, hP₀⟩ : ∃ P₀, D.naut.ptV i P₀ = some x := by
    by_contra hne
    apply hf0
    unfold eigC at hf
    have : (⨆ P ∈ {P | D.naut.ptV i P = some x}, D.naut.typeV i P) = ⊥ :=
      iSup_eq_bot.2 fun P' => iSup_eq_bot.2 fun hP' => absurd ⟨P', hP'⟩ hne
    rw [this] at hf
    exact (Submodule.mem_bot ℂ).1 hf
  obtain ⟨v₀, Dv₀, hov₀⟩ := GlobalTheory.T.exists_inertLocalDatum_at_inertPlace D hA.hF w hin
  obtain ⟨α₀, -, hα₀⟩ := GlobalTheory.EigInert.satParam hL D P i P₀ v₀ w hov₀ hns Dv₀
  refine ⟨P₀, hP₀, ?_⟩
  rw [hn]
  refine ⟨α₀, hα₀, fun τ ϖ hU hc d t hd ht => ?_⟩
  obtain ⟨v, Dv, hov, rfl, rfl, hq, he, hsupp⟩ :=
    exists_datum D.host.F hA.hF D.sp.cm.sig (fun _ => rfl) D.R.nV w hin τ ϖ hU hc
  obtain ⟨R, hR, hop⟩ := exists_sphOp hn (hA.stdV j) hin Dv hc he (triv_iff (hA.stdV j) hsupp) hd t ht
  have hfix := GlobalTheory.T.operator_eigen_good_place_first hAF hL D P X hA h41 h7 htl i hμ j hj h hops w hG hin v hov
  have k1 := heckeFunI_eigC hL D P h41 i x hns hov Dv hfix P₀ hP₀ α₀ hα₀ _
    (Formalism.UG.Final.DosetIndMem _ (Formalism.UG.KU Dv.σw D.R.nV) ℂ t) _ hf
  rw [← hop _ _ (hfix _), hq] at k1
  have k2 := sum_extV X j _ h hops hG hR y _ (hs w _ hG ⟨_, hR⟩)
  obtain ⟨e, hreal⟩ := real_cast hA hμ j _ hj (D.nd.j_range i).1 (D.nd.j_range i).2
  have k3 : ∑ γ ∈ R, NG.rt D.host.E D.R.nV γ ((P.M.loc i).real (hj ▸ f)) =
      s w (List.ofFn d) • (P.M.loc i).real (hj ▸ f) := by
    funext g
    have k4 := congrArg e (k2 ((hA.PV j).ψ ((hA.a j)⁻¹ * g)))
    rw [Finset.sum_image (hA.PV j).inj.injOn, map_sum, map_smul, hy] at k4
    rw [Finset.sum_apply, Pi.smul_apply]
    refine (Finset.sum_congr rfl fun γ _ => ?_).trans (k4.trans (congrArg _ (hreal f g).symm))
    refine (hreal f (g * γ)).trans ?_
    rw [← mul_assoc, map_mul]
  have hne : (P.M.loc i).real (hj ▸ f) ≠ 0 := fun e0 => hf0 ((P.M.loc i).real_inj (e0.trans (map_zero _).symm))
  exact smul_left_injective ℂ hne (k3.symm.trans k1)

end GlobalTheory.InertEigSat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaEigenCompatibilitySecondStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_eigen_compatibility_second : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.adm7 D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i, ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x → ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.UG.IsInertAt D.host.F D.host.E (Pp.under (𝓞 D.host.F)) Pp → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) Pp d → ∃ c : ℂ, h Pp (Finsupp.single d 1) y = c • y := by
  first | exact @GlobalTheory.EigInert.eigen_at_inert | exact GlobalTheory.EigInert.eigen_at_inert | (intros; apply GlobalTheory.EigInert.eigen_at_inert <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaFunctionsSpannedHeckeTwistedStandardFrame
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LinModSpan

theorem isComp_mul_inv {E : Type} [Field E] [NumberField E] {μ η : HChar E} {w : HeightOneSpectrum (𝓞 E)}
    {μw ηw : (w.adicCompletion E)ˣ →* ℂˣ} (hμ : IsComp μ w μw) (hη : IsComp η w ηw) :
    IsComp (μ * η⁻¹) w (μw * ηw⁻¹) := by
  refine ⟨?_, fun x => ?_⟩
  · have h1 := hμ.1
    have h2 := hη.1
    unfold GlobalTheory.SmGL.IsSmoothChar at h1 h2 ⊢
    have h3 : IsOpen (((μw.ker ⊓ ηw.ker : Subgroup _)) : Set (w.adicCompletion E)ˣ) := h1.inter h2
    exact Subgroup.isOpen_mono (H₁ := μw.ker ⊓ ηw.ker) (fun y hy => by
      simp only [Subgroup.mem_inf, MonoidHom.mem_ker] at hy ⊢
      simp [hy.1, hy.2]) h3
  · simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, hμ.2 x, hη.2 x]
    rfl

theorem main : ∀ (D : D7) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ) (V W : Formalism.BasicNotions.TH.HSp D) (n r : ℕ) (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n) (PW : Formalism.IndefR.principalLevelFrame.RowPsi W r) (hF : D.host.F = maximalRealSubfield D.host.E), GlobalTheory.NJoin.StdFrame hF PV → GlobalTheory.NJoin.StdFrame hF PW → ∀ χV χW om, Formalism.IndefR.Datum.IsWeilDatumO ψ V W χV χW om → ∀ μ η : HChar D.host.E, Formalism.IndefR.Links.ChrEq χV μ → Formalism.IndefR.Links.ChrEq χW (μ * η⁻¹) → ∀ (s : SplitPlace D.host.E) μw ηw, IsComp μ s.w μw → IsComp η s.w ηw → ∀ f, Formalism.IndefR.Datum.IsThetaFunO ψ V W f → f ∈ ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion D.host.E)) →ₗ[ℂ] (Formalism.IndefR.Datum.WO V W → ℂ)) (_ : IsLinAt (om.comp (PV.ψ.prodMap PW.ψ)) s μw ηw ι ∧ ∀ Φ, Formalism.IndefR.Datum.IsThetaFunO ψ V W (ι Φ)), LinearMap.range ι := by
  intro D ψ V W n r PV PW hF hV hW χV χW om hom μ η hμ hη s μw ηw hμw hηw f hf
  obtain ⟨p, hpe, hpr, FS, FT, c, hc, hci, hlocV, hlocW⟩ := GlobalTheory.T.standardFrames_read_splitPlace_unitaryGroup D V W n r PV PW hF hV hW s
  have cV := GlobalTheory.T.localComponent_of_idelicCharacterAgreement D s p hpe hpr χV μ hμ μw hμw
  have cW := GlobalTheory.T.localComponent_of_idelicCharacterAgreement D s p hpe hpr χW (μ * η⁻¹) hη (μw * ηw⁻¹) (isComp_mul_inv hμw hηw)
  obtain ⟨τ, hτ, hτom⟩ := GlobalTheory.T.linearModel_fourier_transform_exchange (s.w.adicCompletion D.host.E) n r
  have hOm := GlobalTheory.T.weilDatum_localModel_formula D
  have h2 := GlobalTheory.T.thetaFunction_mem_span_localSchrodingerModels_split D _ p (Fin r) (Fin n) V W FS FT ψ hom.std f hf
  refine (iSup₂_le fun Tm hTm => ?_ : (⨆ (Tm : GlobalTheory.SplitWeil.SB (Matrix (Fin r) (Fin n) (s.w.adicCompletion D.host.E)) →ₗ[ℂ] (Formalism.IndefR.Datum.WO V W → ℂ)) (_ : p.IsModel ψ FS FT Tm), LinearMap.range Tm) ≤ _) h2
  have hr : LinearMap.range Tm = LinearMap.range (Tm ∘ₗ τ) := by
    rw [LinearMap.range_comp, LinearMap.range_eq_top.2 hτ, Submodule.map_top]
  rw [hr]
  refine le_iSup₂_of_le (f := fun (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion D.host.E)) →ₗ[ℂ] (Formalism.IndefR.Datum.WO V W → ℂ)) (_ : IsLinAt (om.comp (PV.ψ.prodMap PW.ψ)) s μw ηw ι ∧ ∀ Φ, Formalism.IndefR.Datum.IsThetaFunO ψ V W (ι Φ)) => LinearMap.range ι) (Tm ∘ₗ τ) ⟨?_, fun Φ => hTm.theta _⟩ le_rfl
  refine ⟨c, hc, hci, fun h g hh hg Φ Φ' hΦ => ?_⟩
  have hΦ'' : Φ'.1 = GlobalTheory.SplitWeil.om μw (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc r g)) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h)) Φ.1 := hΦ
  have key := hOm (s.w.adicCompletion D.host.E) p ψ V W χV χW om hom μw (μw * ηw⁻¹) cV cW (Fin r) (Fin n) FS FT Tm hTm
    (PV.ψ h) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h)) (PW.ψ g) (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc r g))
    (hlocV h hh) (hlocW g hg) (τ Φ)
    (((ηw (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n h))) : ℂˣ) : ℂ) • τ Φ') (by
      rw [Submodule.coe_smul, hτom μw _ _ Φ Φ' hΦ'']
      congr 2
      simp [mul_inv_rev, mul_comm])
  simp only [LinearMap.comp_apply, MonoidHom.comp_apply]
  show om (PV.ψ h, PW.ψ g) (Tm (τ Φ)) = _
  rw [key, map_smul]

end GlobalTheory.LinModSpan
end

