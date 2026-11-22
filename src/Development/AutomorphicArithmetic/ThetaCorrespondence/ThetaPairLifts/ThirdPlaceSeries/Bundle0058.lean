import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExtensionVectorThetaCompatible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0018
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0001
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0408
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0051
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0048
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0035
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0033
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0039
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0361

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TransportAlt
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.EigTransport
end GlobalTheory.EigTransport
namespace GlobalTheory.EigTransport
end GlobalTheory.EigTransport
namespace GlobalTheory.EigTransport
end GlobalTheory.EigTransport
namespace GlobalTheory.EigTransport
end GlobalTheory.EigTransport
namespace GlobalTheory.EigTransport
end GlobalTheory.EigTransport
namespace GlobalTheory.EigTransport
theorem transport_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ (s : GlobalTheory.DownLift.Sys D), GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) h s y → ∀ sp : SplitPlace D.host.E, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) sp.w → (∀ κ : GAf D.host.E D.R.nV, TrivOutside {sp.v} κ → (κ ∈ (P.M.loc i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ hκ : κ ∈ (P.M.loc i).J, (P.M.loc i).χ ⟨κ, hκ⟩ = 1) → ∀ ϖ, IsUnif D.host.E sp.v ϖ → ∀ k ≤ D.R.nV, NG.heckeD (P.M.loc i).J (Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k) ((P.M.loc i).real (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i))) = s sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0) • (P.M.loc i).real (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) := by
  intro _ hL D P X A _ _ _ i hμ j hj f y hy h hOps s hEig sp hG hJ ϖ hϖ k hk
  have hn : (Formalism.IndefR.Links.Vc D j).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) j.2
  have hLab := isLab_std A.hF (A.PV j) (A.stdV j) hn sp ϖ hϖ k hk
  have hsum := eig_sum X hμ j f y hy h hOps s hEig sp.w hG (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0) hLab
  have hGf := GlobalTheory.DefLiftHecke.rep_mem_GfC (Formalism.IndefR.Links.Vc D j) sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0)
  classical
  let xi : Formalism.L2.Theta.GA D (Formalism.IndefR.Links.Vc D j) → Formalism.AUTREP.GAf D.host.E D.R.nV := fun γ =>
    if hγ : γ ∈ Formalism.L2.Theta.GfC (Formalism.IndefR.Links.Vc D j) then ((A.PV j).onto γ hγ).choose else 1
  have hxi : ∀ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0), (A.PV j).ψ (xi γ) = γ := fun γ hγ => by
    simp only [xi, dif_pos (hGf γ hγ)]
    exact ((A.PV j).onto γ (hGf γ hγ)).choose_spec
  have hT : ∀ x ∈ Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k, TrivOutside {sp.v} x := fun x hx => hx.1
  suffices key : ∀ (m : ℕ) (e : j.1 + 1 = m) (p1 : 1 ≤ m) (p2 : m ≤ D.R.m),
      (∀ κ : Formalism.AUTREP.GAf D.host.E D.R.nV, TrivOutside {sp.v} κ →
        (κ ∈ (P.M (D.nd.mu i) m p1 p2).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧
          ∀ hκ : κ ∈ (P.M (D.nd.mu i) m p1 p2).J, (P.M (D.nd.mu i) m p1 p2).χ ⟨κ, hκ⟩ = 1) →
      NG.heckeD (P.M (D.nd.mu i) m p1 p2).J (Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k)
          ((P.M (D.nd.mu i) m p1 p2).real (e ▸ f)) =
        s sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0) • (P.M (D.nd.mu i) m p1 p2).real (e ▸ f) from key _ hj _ _ hJ
  intro m e
  subst e
  intro p1 p2 hJ
  have hF : ∀ g, (P.M (D.nd.mu i) (j.1 + 1) p1 p2).real f g =
      A.eW _ hμ j (X.fn hμ j f ((A.PV j).ψ ((A.a j)⁻¹ * g))) := fun g => A.real (D.nd.mu i) hμ j f g
  have hinv : ∀ κ (hκ : κ ∈ (P.M (D.nd.mu i) (j.1 + 1) p1 p2).J), (P.M (D.nd.mu i) (j.1 + 1) p1 p2).χ ⟨κ, hκ⟩ = 1 →
      ∀ g, (P.M (D.nd.mu i) (j.1 + 1) p1 p2).real f (g * κ) = (P.M (D.nd.mu i) (j.1 + 1) p1 p2).real f g := by
    intro κ hκ h1 g
    have hmem : (P.M (D.nd.mu i) (j.1 + 1) p1 p2).real f ∈ Formalism.L2.NG.TypeSp (P.M (D.nd.mu i) (j.1 + 1) p1 p2).wt.ρ
        (P.M (D.nd.mu i) (j.1 + 1) p1 p2).J (P.M (D.nd.mu i) (j.1 + 1) p1 p2).χ := by
      rw [← (P.M (D.nd.mu i) (j.1 + 1) p1 p2).real_range]
      exact LinearMap.mem_range_self _ _
    have := congrFun (hmem.2 ⟨κ, hκ⟩) g
    rw [h1] at this
    simp only [Units.val_one, one_smul] at this
    exact this
  have hmemT : ∀ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0), xi γ ∈ Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k := by
    intro γ hγ
    refine (tSet_iff A.hF (A.PV j) (A.stdV j) hn sp ϖ hϖ k hk _).2 ⟨γ, hγ, ?_⟩
    rw [hxi γ hγ, inv_mul_cancel]
    exact GlobalTheory.DefLiftHecke.one_mem_hyp _ _
  funext g
  show (∑ᶠ c : Formalism.AUTREP.GAf D.host.E D.R.nV ⧸ (P.M (D.nd.mu i) (j.1 + 1) p1 p2).J,
      if hc : ∃ x ∈ Formalism.AUTREP.tSet D.host.E D.R.nV sp ϖ k,
          (x : Formalism.AUTREP.GAf D.host.E D.R.nV ⧸ (P.M (D.nd.mu i) (j.1 + 1) p1 p2).J) = c then
        (P.M (D.nd.mu i) (j.1 + 1) p1 p2).real f (g * hc.choose) else 0) = _
  rw [finsum_cosets (P.M (D.nd.mu i) (j.1 + 1) p1 p2).J _ (GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0)) xi _
    ?h1 ?h2 ?h3 ?h4 g]
  case h1 => exact hmemT
  case h2 =>
    intro x hx
    obtain ⟨γ, hγ, hm⟩ := (tSet_iff A.hF (A.PV j) (A.stdV j) hn sp ϖ hϖ k hk x).1 hx
    refine ⟨γ, hγ, ?_⟩
    rw [← hxi γ hγ, ← map_inv, ← map_mul] at hm
    obtain ⟨hU, hT'⟩ := (frame_hyp A.hF (A.PV j) (A.stdV j) sp _).1 hm
    exact (hJ _ hT').1.2 hU
  case h3 =>
    intro γ hγ γ' hγ' hm
    have ht := triv_mul (triv_inv (hT _ (hmemT γ hγ))) (hT _ (hmemT γ' hγ'))
    have hU := (hJ _ ht).1.1 hm
    have hh := (frame_hyp A.hF (A.PV j) (A.stdV j) sp _).2 ⟨hU, ht⟩
    rw [map_mul, map_inv, hxi γ hγ, hxi γ' hγ'] at hh
    exact rep_inj _ _ _ hLab γ hγ γ' hγ' hh
  case h4 =>
    intro y hy y' hy' hm g0
    have ht := triv_mul (triv_inv (hT _ hy)) (hT _ hy')
    have := hinv _ hm ((hJ _ ht).2 hm) (g0 * y)
    rw [mul_assoc, mul_inv_cancel_left] at this
    exact this
  rw [Pi.smul_apply, hF g]
  calc ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0), (P.M (D.nd.mu i) (j.1 + 1) p1 p2).real f (g * xi γ)
      = ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0),
          A.eW _ hμ j (X.fn hμ j f ((A.PV j).ψ ((A.a j)⁻¹ * g) * γ)) :=
        Finset.sum_congr rfl fun γ hγ => by rw [hF, ← mul_assoc, map_mul, hxi γ hγ]
    _ = A.eW _ hμ j (∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w (List.replicate k 1 ++ List.replicate (D.R.nV - k) 0),
          X.fn hμ j f ((A.PV j).ψ ((A.a j)⁻¹ * g) * γ)) := (map_sum _ _ _).symm
    _ = _ := by rw [hsum, map_smul]
end GlobalTheory.EigTransport
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnderInjective
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam.PlaceInj
theorem under_injective_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → Function.Injective (fun i : {PP // PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP} => HeightOneSpectrum.under (𝓞 D.host.F) i.1) := by
  intro D L hT Gi Gl Kc Yd cX ex W hW
  have lev : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.Is W.P.A3.A.μ0 := hW.bot.hyp.2.2.2.1.lev
  rintro ⟨P, hP⟩ ⟨P', hP'⟩ h
  simp only at h
  apply Subtype.ext
  show P = P'
  have key : ∀ A B : Formalism.L2.DIV.Pl D.host.E, A ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg → (B ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W B) →
      A.under (𝓞 D.host.F) = B.under (𝓞 D.host.F) → A = B := by
    intro A B hA hB hAB
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hAB.symm with e | e
    · exact e.symm
    · exfalso
      have hc : Formalism.IndefR.Lev.IsConjPl A B := GlobalTheory.GoodPrimes.isConjPl_iff.2 e
      rcases hB with hB | ⟨t, hB⟩
      · exact (GlobalTheory.ChainEquiv.places_sep _ _ lev W.P.A3.A.μ0).1 A hA B (Or.inl hB) hc
      · exact (GlobalTheory.ChainEquiv.places_sep _ _ lev t).1 A hA B (Or.inr hB) hc
  rcases hP with hP | hP
  · exact key P P' hP hP' h
  · rcases hP' with hP' | hP'
    · exact (key P' P hP' (Or.inr hP) h.symm).symm
    · exact hW.sel P P' hP hP' h
end GlobalTheory.Fam.PlaceInj
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeilOKFam
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam.WeilTup
variable {D : D7}
theorem weilOK_fam_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (v : VCom f.c), f.RowOK → f.ColOK → (∀ j h, f.c.Lz.rank = 1 ∧ (v.τ j h)ᴴ * ((f.c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • f.c.Lz.gram) → ∀ t, WeilOK (t := f.t t) v := by
  intro D L hT Gi Gl Kc Yd cX ex W u hP f v hR hC hτ t
  have hmE : ¬ Odd D.R.m := by
    obtain ⟨a, ha⟩ := D.R.m_even
    rintro ⟨b, hb⟩
    omega
  have hE := GlobalTheory.WeilDatumExistence.weilDatumExists D
  have hX := hP.bot.hyp.2.2.2.1.chain.ωX t
  simp only [Formalism.IndefR.Lift.chrStep, if_neg hmE] at hX
  have hη : ∀ j' (h' : j' + 2 * 0 + 2 = D.R.m), IsHeckeChar D (_root_.GlobalTheory.Fam.pk_z W).eta ∧ ResEta D (_root_.GlobalTheory.Fam.pk_z W).eta 1 := by
    intro j' h'
    have e : j' + 1 + 1 = D.R.m := by omega
    have hk := hC.kom t (j' + 1) (by omega)
    have hμH : IsHeckeChar D ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t D.R.m) := by
      have h1 : IsHeckeChar D ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j' + 1 + 1)) := hk.hecS
      rw [e] at h1; exact h1
    have hμR : ResEta D ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t D.R.m) (D.sp.X'.rank + 1) := by
      have h1 : ResEta D ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j' + 1 + 1)) (D.sp.X (j' + 1 + 1)).rank := hk.resT
      have h2 : D.sp.X'.rank + f.c.Lz.rank = (D.sp.X (j' + 1 + 1)).rank := (f.c.oT (j' + 1 + 1) e).rank_add
      rw [← h2, (hτ j' h').1, e] at h1
      exact h1
    have hH : IsHeckeChar D (_root_.GlobalTheory.Fam.pk_z W).eta := by
      have h1 := hecke_mul (hecke_inv hX.hecT) hμH
      rwa [_root_.mul_inv_rev, inv_inv, inv_mul_cancel_right] at h1
    exact ⟨hH, resEta_of_diff hμR hX.resT⟩
  refine ⟨?_, ?_, hτ⟩
  · intro j σ h
    obtain ⟨hHη, hRη⟩ := hη (j + 2 * σ + 2) (by omega)
    have hzH := hecke_inv hHη
    have hzR := Formalism.L2.Theta.resEta_inv hRη
    have hk0 := hC.kom t j (by omega)
    have hk1 := hC.kom t (j + 1) (by omega)
    obtain ⟨-, -, bV, bW⟩ := (hR.row t).sBF j (σ + 1) h
    obtain ⟨-, -, fV, fW⟩ := (hR.row t).sFB j σ h
    have hL := (f.c.bes j (σ + 1) h).line.1
    have hL' := (f.c.bes (j + 1 + 1) σ (idx_step h)).line.1
    obtain ⟨omz, homz⟩ := hE (f.c.bes j (σ + 1) h).L (D.sp.X (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹ ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1))
      hk0.std hzH hk0.hecT (by rw [hL]; exact hzR) hk0.resT
    obtain ⟨omz', homz'⟩ := hE (D.sp.X (j + 1)) (f.c.bes (j + 1 + 1) σ (idx_step h)).L (_root_.GlobalTheory.Fam.pk_z W).ψ ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1))
      (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹ hk1.std hk1.hecS hzH hk1.resS (by rw [hL']; exact hzR)
    refine ⟨(_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1), (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1), (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹, omz, omz', bV, fW, ?_, ?_, ?_, ?_⟩
    · rw [bW]; exact hk0
    · rw [bW]; exact homz
    · rw [fV]; exact hk1
    · rw [fV]; exact homz'
  · intro j h
    have e : j + 1 + 1 = D.R.m := by omega
    obtain ⟨hHη, hRη⟩ := hη j h
    have hzH := hecke_inv hHη
    have hzR := Formalism.L2.Theta.resEta_inv hRη
    have hk0 := hC.kom t j (by omega)
    have hk1 := hC.kom t (j + 1) (by omega)
    obtain ⟨-, -, bV, bW⟩ := (hR.row t).sBF j 0 h
    have hL := (f.c.bes j 0 h).line.1
    have hXH : IsHeckeChar D ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1) * (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹) := by rw [e]; exact hX.hecT
    have hXR : ResEta D ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1) * (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹) D.sp.X'.rank := by rw [e]; exact hX.resT
    obtain ⟨omz, homz⟩ := hE (f.c.bes j 0 h).L (D.sp.X (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹ ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1))
      hk0.std hzH hk0.hecT (by rw [hL]; exact hzR) hk0.resT
    obtain ⟨omT', homT⟩ := hE (D.sp.X (j + 1)) D.sp.X' (_root_.GlobalTheory.Fam.pk_z W).ψ ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1))
      ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1) * (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹) hk1.std hk1.hecS hXH hk1.resS hXR
    obtain ⟨omz'', homz''⟩ := hE (D.sp.X (j + 1)) f.c.Lz (_root_.GlobalTheory.Fam.pk_z W).ψ ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1)) (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹⁻¹
      hk1.std hk1.hecS (by rw [inv_inv]; exact hHη) hk1.resS (by rw [(hτ j h).1, inv_inv]; exact hRη)
    have hμ1 : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1) * (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹ * (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹⁻¹ = (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1) := by
      rw [inv_inv, inv_mul_cancel_right]
    have key : ∀ n (e' : D.R.m - 1 = n), IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D n) D.sp.X' ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1))
        ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1) * (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹)
        (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') ((_root_.GlobalTheory.Fam.pk_z W).ωX t) e') := by
      intro n e'
      subst e'
      rw [e]
      exact hX
    refine ⟨(_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1), (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹, (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1),
      (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu t (j + 1 + 1) * (_root_.GlobalTheory.Fam.pk_z W).eta⁻¹, omz, omT', omz'', bV, ?_, ?_, ?_, homT, key (j + 1) (idx_top h), homz''⟩
    · rw [bW]; exact hk0
    · rw [bW]; exact homz
    · rw [hμ1]; exact hk1
end GlobalTheory.Fam.WeilTup
end
end
end

