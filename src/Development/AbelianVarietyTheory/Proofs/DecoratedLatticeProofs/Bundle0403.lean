import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0270
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LambdaZeroEqProduct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0284
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0385
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0294
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0301
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0302
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1451
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0003
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0349
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSubMulComplementEqComplement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0387
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGAtAllPlacesMul
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SeeSaw ValuativeRel GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.PinInhab

section SlopeTestRemainingChoices
open GlobalTheory.FinPl (SplitPt idAt idOff grpAt grpOff congGrp compAt)
open GlobalTheory.IdemSupport GlobalTheory.LocMod.SevPl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem e_mul_add (q : SplitPt D k) : q.e * (q.e + cA D q.e) = q.e := by
  obtain ⟨h1, h2, -⟩ := q.split
  rw [mul_add, h1, h2, add_zero]

theorem v_eq_under (q : SplitPt D k) {P : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.L2.NTheta.IsIdemAt q.e P) :
    q.v = P.under (𝓞 D.host.F) := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨ε, hε, hs⟩ := q.above
  by_contra hne
  have h0 := (place_comp hΦ hε).2.2 P (fun e => hne e.symm)
  have h1 := ev_mul (Φ := Φ) q.e (q.e + cA D q.e) P
  rw [e_mul_add, hs, h0, mul_zero, (delta_of_isIdemAt hΦ h).2.1] at h1
  exact one_ne_zero h1

theorem idem_unique {P : HeightOneSpectrum (𝓞 D.host.E)} {e e' : Formalism.L2.Theta.AE D} (h : Formalism.L2.NTheta.IsIdemAt e P)
    (h' : Formalism.L2.NTheta.IsIdemAt e' P) : e = e' := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have hd := delta_of_isIdemAt hΦ h
  have hd' := delta_of_isIdemAt hΦ h'
  refine hΦ.ext' (by rw [hd.1, hd'.1]) fun Q => ?_
  by_cases hQ : Q = P
  · subst hQ; rw [hd.2.1, hd'.2.1]
  · rw [hd.2.2 Q hQ, hd'.2.2 Q hQ]

theorem mem_congGrp {V : HSp D} {I : Ideal (Formalism.L2.Theta.AE D)} {g : GA D V} :
    g ∈ congGrp V I ↔ ∀ i j, (mt V g - 1) i j ∈ I := by
  unfold congGrp
  rw [MonoidHom.mem_ker]
  constructor
  · intro h i j
    have := congrArg (fun x : GL (Fin V.rank) (Formalism.L2.Theta.AE D ⧸ I) => x.1 i j) h
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
    simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
    exact this
  · intro h
    ext i j
    have := h i j
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq] at this
    simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
    exact this

theorem mem_idAt_of_supp (q : SplitPt D k) {P : GlobalTheory.FinPl.Pl D → Prop} (hP : P q.v) {a : Formalism.L2.Theta.AE D}
    (h : (q.e + cA D q.e) * a = a) : a ∈ idAt D P := by
  obtain ⟨ε, hε, hs⟩ := q.above
  have h1 := ((GlobalTheory.FinPl.placeIdem_acts D q.v ε hε).1 a).2 (hs ▸ h)
  rw [GlobalTheory.FinPl.mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at h1 ⊢
  exact ⟨h1.1, fun w hw => h1.2 w fun e => hw (e ▸ hP)⟩

theorem mem_grpAt_of_supp (q : SplitPt D k) {P : GlobalTheory.FinPl.Pl D → Prop} (hP : P q.v) {V : HSp D} {g : GA D V}
    (hg : SuppAt q.e V g) : g ∈ grpAt V P :=
  mem_congGrp.2 fun i j => mem_idAt_of_supp q hP (hg i j)

theorem pr_eq_zero_of_off (q : SplitPt D k) {P : GlobalTheory.FinPl.Pl D → Prop} (hP : P q.v) {a : Formalism.L2.Theta.AE D}
    (ha : a ∈ idOff D P) : q.pr a = 0 := by
  have he : q.e ∈ idAt D (· = q.v) := mem_idAt_of_supp q (P := (· = q.v)) rfl (by rw [mul_comm, e_mul_add])
  rw [GlobalTheory.FinPl.mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at he
  have hv : compAt D q.v a = 0 := by
    unfold idOff at ha
    rw [Submodule.mem_iInf] at ha
    exact RingHom.mem_ker.1 (ha ⟨q.v, hP⟩)
  refine pr_eq_zero q (GlobalTheory.FinPl.CMAdele_eq_zero_of_infinite_and_finite_components_zero D _ ?_ fun w => ?_)
  · rw [RingHom.map_mul, he.1, zero_mul]
  · rw [RingHom.map_mul]
    by_cases hw : w = q.v
    · rw [hw, hv, mul_zero]
    · rw [he.2 w hw, zero_mul]

theorem map_mt_eq_one_of_off (q : SplitPt D k) {P : GlobalTheory.FinPl.Pl D → Prop} (hP : P q.v) {V : HSp D} {g : GA D V}
    (hg : g ∈ grpOff V P) : (mt V g).map q.pr = 1 := by
  ext i j
  have h1 := pr_eq_zero_of_off q hP (mem_congGrp.1 hg i j)
  rw [Matrix.sub_apply, map_sub] at h1
  rw [Matrix.map_apply, sub_eq_zero.1 h1]
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.one_apply_ne hij]

theorem exists_gAt_all_places_mul : ∀ (D : D7) (u : D.what₂.Word) (d : Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E), d.c.Is → (∀ PP : d.c.Pg, ∃ (e : Formalism.L2.Theta.AE D) (t : ∀ j, GA D (d.st j).V), Formalism.L2.NTheta.IsIdemAt e PP.1 ∧ (∀ j, SuppAt e (d.st j).V (t j)) ∧ Nonempty (GAt (d := { d with t := t }) τ PP.1)) → ∀ t₀ : ∀ j, GA D (d.st j).V, (∀ j, t₀ j ∈ GlobalTheory.FinPl.grpOff (d.st j).V (· ∈ d.c.S)) → ∃ t' : ∀ j, GA D (d.st j).V, (∀ j, t' j * (t₀ j)⁻¹ ∈ GlobalTheory.FinPl.grpAt (d.st j).V (· ∈ d.c.S)) ∧ (∀ j, t₀ j ∈ GfC (d.st j).V → t' j ∈ GfC (d.st j).V) ∧ Nonempty (∀ PP : d.c.Pg, GAt (d := { d with t := t' }) τ PP.1) := by
  intro D u d τ hIs h t₀ ht₀
  classical
  have h' : ∀ PP : d.c.Pg, ∃ (t : ∀ j, GA D (d.st j).V) (G : GAt (d := { d with t := t }) τ PP.1),
      ∀ j, SuppAt G.q.e (d.st j).V (t j) := fun PP => by
    obtain ⟨e, t, he, ht, ⟨G⟩⟩ := h PP
    exact ⟨t, G, by rw [idem_unique G.idem he]; exact ht⟩
  choose T G hS using h'
  obtain ⟨E, hE⟩ := hIs.split
  have hv : ∀ PP : d.c.Pg, (G PP).q.v ∈ d.c.S := fun PP => by
    rw [v_eq_under (G PP).q (G PP).idem]
    exact Finset.mem_image_of_mem _ PP.2
  let t' : ∀ j, GA D (d.st j).V := fun j => (d.c.Pg.attach.toList.map fun PP => T PP j).prod * t₀ j
  refine ⟨t', fun j => ?_, fun j h0 => mul_mem (list_prod_mem fun x hx => ?_) h0, ⟨fun PP => ?_⟩⟩
  · rw [mul_inv_cancel_right]
    refine list_prod_mem fun x hx => ?_
    obtain ⟨Q, -, rfl⟩ := List.mem_map.1 hx
    exact mem_grpAt_of_supp (G Q).q (hv Q) (hS Q j)
  · obtain ⟨Q, -, rfl⟩ := List.mem_map.1 hx
    exact GlobalTheory.WeilProduct.mem_GfC_of_suppAt (G Q).q.split (hS Q j)
  have key : ∀ j, (mt (d.st j).V (t' j)).map (ofSplit (G PP).q).π =
      (mt (d.st j).V (T PP j)).map (ofSplit (G PP).q).π := by
    intro j
    change locHom (ofSplit (G PP).q).π (d.st j).V _ = locHom (ofSplit (G PP).q).π (d.st j).V _
    have h0 : locHom (ofSplit (G PP).q).π (d.st j).V (t₀ j) = 1 := map_mt_eq_one_of_off (G PP).q (hv PP) (ht₀ j)
    rw [map_mul, h0, mul_one, map_list_prod, List.map_map]
    refine prod_map_single _ PP _ (Finset.nodup_toList _) (Finset.mem_toList.2 (Finset.mem_attach _ _)) fun PP' _ hne => ?_
    exact map_mt_eq_one _ _ _ (hS PP' j) (pr_eq_zero (G PP).q
      (mul_conj_add_eq_zero hE PP.2 PP'.2 (fun h => hne (Subtype.ext h).symm) (G PP).idem (G PP').idem))
  have hfr : ∀ j c (hc : j + c = (G PP).s + 1), ∃ e : Ix (Fin D.R.k ⊕ Fin ((G PP).s + 1)) (Fin D.R.t) j ≃ Fin (d.st j).V.rank,
      GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit (G PP).q) (d.st j).V (t' j) (d.st j).β
        ((((G PP).FY j c hc).β * (((G PP).S.T (Fin D.R.t)).bas j c hc).val).submatrix id
          fun i => stdOrd (Fin D.R.k) (Fin D.R.t) j c hc (e.symm i)) := by
    intro j c hc
    obtain ⟨e, ho, hm⟩ := (G PP).frame j c hc
    refine ⟨e, ho, fun b hb => ?_⟩
    refine Eq.trans ?_ (hm b hb)
    rw [Matrix.map_mul, Matrix.map_mul]
    exact congrArg (· * b.map _) (key j)
  exact { G PP with frame := hfr }

end SlopeTestRemainingChoices

theorem main :
    (∀ (D : D7) (u : D.what₂.Word) (d : Dat D u) τ (G : ∀ PP : d.c.Pg, GAt d τ PP.1), d.c.Is → (∃ P : Formalism.L2.DIV.LevelP d.c.Pg D.R.r ℂ, (∀ g, g ∈ P.H ↔ ∀ PP, ∃ x, (G PP).Red x (g PP)) ∧ ∀ (g : P.H) (x : ∀ PP, (G PP).S.P.J), (∀ PP, (G PP).Red (x PP) (g.1 PP)) → P.chi g = ∏ PP, (G PP).S.P.lam (x PP)) ∧ ∃ cG : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ, (∀ j, ∀ w ∈ (cG j).support, GlobalTheory.FinPl.MxAt (· ∈ d.c.S) w) ∧ ∀ j, j < D.R.m → ∀ f, IsThetaFunO d.c.ψ _ _ f → comb d.c.ψ _ _ (cG j) f = d.c.Pg.attach.toList.foldr (fun PP f' => comb d.c.ψ _ _ ((G PP).cg j) f') f) ∧
    (∀ (D : D7) (u : D.what₂.Word) (d : Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E), d.c.Is → (∀ PP : d.c.Pg, ∃ (t : ∀ j, GA D (d.st j).V) (G : GAt (d := { d with t := t }) τ PP.1), ∀ j, SuppAt G.q.e (d.st j).V (t j)) → ∀ t₀ : ∀ j, GA D (d.st j).V, (∀ j, t₀ j ∈ GlobalTheory.FinPl.grpOff (d.st j).V (· ∈ d.c.S)) → ∃ t' : ∀ j, GA D (d.st j).V, (∀ j, t' j * (t₀ j)⁻¹ ∈ GlobalTheory.FinPl.grpAt (d.st j).V (· ∈ d.c.S)) ∧ (∀ j, t₀ j ∈ GfC (d.st j).V → t' j ∈ GfC (d.st j).V) ∧ Nonempty (∀ PP : d.c.Pg, GAt (d := { d with t := t' }) τ PP.1)) ∧
    (∀ (D : D7) (u : D.what₂.Word) (d : Dat D u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), d.c.Is → PP ∈ d.c.Pg → Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ ψk : AddChar k Circle, (ofSplit q).IsChar d.c.ψ ψk → HasConductor ψk 1 → ∀ s ρ : ℕ, s = 2 * ρ → ∃ S : SymData k s D.R.k, S.ψ = ψk ∧ ∀ j, 1 ≤ j → j ≤ D.R.m → (ofSplit q).IsComp (d.c.chS j)⁻¹ (S.μ j)) ∧
    (∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (Y : Type) [Fintype Y] [DecidableEq Y], q.UnitAA → Submodule.IsLattice D.host.E L → Fintype.card Y = S.rank → ∃ F : GlobalTheory.LocMod.Frame k S.rank Y, ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((F.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S L (· = q.v)) ∧
    (∀ (D : D7) (u : D.what₂.Word) (d : Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (s : ℕ) (hs : s + 1 + 1 = D.R.m), d.Lz.rank = 1 → Fintype.card (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2)) = D.sp.X'.rank → ∀ (a : k) (z₀ : Fin d.Lz.rank → k), valuation k a = 1 → (∀ h, (τ s h).map (ofSplit q).pr *ᵥ z₀ = (-((ofSplit q).xi * a)) • fun i => (ofSplit q).pr ((d.bes s 0 h).ζ i)) → (∀ B : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) (AE D), B.map (toEAf D) = d.top.β.val → ∀ (y : Fin D.sp.X'.rank → k) (b : k), (fun i => q.sec (((d.oT (s + 1 + 1) hs).iA.map (ofSplit q).pr *ᵥ (B.map (ofSplit q).π *ᵥ y) + b • ((d.oT (s + 1 + 1) hs).iB.map (ofSplit q).pr *ᵥ z₀)) i)) ∈ GlobalTheory.FinPl.latV (D.sp.X (s + 1 + 1)) (d.x (s + 1 + 1)).L (· = q.v) ↔ (∀ i, y i ∈ 𝒪[k]) ∧ b ∈ 𝒪[k]) → ∃ (FT : GlobalTheory.LocMod.Frame k D.sp.X'.rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2))) (FM : GlobalTheory.LocMod.Frame k (D.sp.X (s + 1 + 1)).rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit)) (c : k), valuation k c = 1 ∧ FM.β = fromCols ((d.oT (s + 1 + 1) hs).iA.map (ofSplit q).pr * FT.β) (Matrix.of fun r _ => ((d.oT (s + 1 + 1) hs).iB.map (ofSplit q).pr *ᵥ z₀) r) ∧ (∀ h, (τ s h).map (ofSplit q).pr *ᵥ z₀ = (-((ofSplit q).xi * c)) • fun i => (ofSplit q).pr ((d.bes s 0 h).ζ i)) ∧ (∀ y : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FM.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV (D.sp.X (s + 1 + 1)) (d.x (s + 1 + 1)).L (· = q.v)) ∧ ∃ e : Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ≃ Fin D.sp.X'.rank, GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e ∧ MovedTo (ofSplit q) D.sp.X' 1 d.top.β (FT.β.submatrix id e.symm)) ∧
    (∀ (D : D7) (u : D.what₂.Word) (d : Dat D u) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (q : GlobalTheory.FinPl.SplitPt D k) (s : ℕ) (S : SymData k s D.R.k) (FX : ∀ j, j ≤ s + 1 → GlobalTheory.LocMod.Frame k (D.sp.X j).rank (XIx (Fin D.R.k) (Fin D.R.t) j)) (FM : GlobalTheory.LocMod.Frame k (D.sp.X (s + 1 + 1)).rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit)), IsStdChar D d.c.ψ (-1) → ∃ cg : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ, (∀ j c (H : j + 1 + c = s), (ofSplit q).IsCombAt d.c.ψ (FX j (by omega)) (FX (j + 1) (by omega)) (cg j) ((S.T (Fin D.R.t)).entry S.ψ ν j c H 1 1)) ∧ (ofSplit q).IsCombAt d.c.ψ (FX s (by omega)) (FX (s + 1) le_rfl) (cg s) (fun x₀ => (S.T (Fin D.R.t)).Psi 1 x₀ (S.y0 (Fin D.R.t))) ∧ (ofSplit q).IsCombAt d.c.ψ (FX (s + 1) le_rfl) FM (cg (s + 1)) ((S.T (Fin D.R.t)).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 (Fin D.R.t))))) :=
  ⟨GlobalTheory.LevelComb.main,
    fun D u d τ hIs h => exists_gAt_all_places_mul D u d τ hIs fun PP =>
      let ⟨t, G, ht⟩ := h PP
      ⟨G.q.e, t, G.idem, ht, ⟨G⟩⟩,
    GlobalTheory.T.exists_symmetric_data_conductor_one, GlobalTheory.LocMod.FullLatFrame.exists_frame, GlobalTheory.LocMod.TopFrames.top_frames, GlobalTheory.LocMod.CombAt.exists_cg⟩

end GlobalTheory.LocMod.PinInhab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormOneIdeleWithSplitPlaceComponent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

set_option maxHeartbeats 2000000 in
open GlobalTheory.FinPl.FrameLat in

theorem exists_normOneAt_pr (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : SplitPt D k) (c₀ : k) (hc₀ : c₀ ≠ 0) :
    ∃ c : AE D, NormOneAt p.v c ∧ p.pr c = c₀ := by
  have hf : ∀ x : k, (p.e + cA D p.e) * p.sec x = p.sec x := fun x => (idem_iff p _).1 (sec_mem_idAt p x)
  have hcf : ∀ x : k, (p.e + cA D p.e) * cA D (p.sec x) = cA D (p.sec x) :=
    fun x => (idem_iff p _).1 (csec_mem_idAt (p := p) x)
  have hee : p.e * cA D p.e = 0 := p.split.2.1
  have hce : cA D p.e * p.e = 0 := cAe_mul_e p
  have hecs : ∀ x : k, p.e * cA D (p.sec x) = 0 := by
    intro x
    rw [← e_mul_sec p x, map_mul, ← mul_assoc, hee, zero_mul]
  have hsc : ∀ x y : k, p.sec x * cA D (p.sec y) = 0 := by
    intro x y
    rw [← e_mul_sec p x, mul_comm p.e, mul_assoc, hecs, mul_zero]
  have hprc : ∀ x : k, p.pr (cA D (p.sec x)) = 0 := by
    intro x
    have h1 : p.sec (p.pr (cA D (p.sec x))) = 0 := by rw [p.sec_pr, hecs]
    have h2 := congrArg p.pr h1
    rwa [p.pr_sec, map_zero] at h2
  have hcc : ∀ z : AE D, cA D (cA D z) = z := fun z => cA_cA z
  have he1 : p.sec 1 = p.e := sec_one p
  obtain ⟨f, hfdef⟩ : ∃ f : AE D, f = p.e + cA D p.e := ⟨_, rfl⟩
  have hfm : f ∈ idAt D (· = p.v) := hfdef ▸ sum_mem_idAt p
  have hff : f * f = f := by
    have := (idem_iff p f).1 hfm; rwa [← hfdef] at this
  have hf' : ∀ x : k, f * p.sec x = p.sec x := fun x => hfdef ▸ hf x
  have hcf' : ∀ x : k, f * cA D (p.sec x) = cA D (p.sec x) := fun x => hfdef ▸ hcf x

  obtain ⟨u, hu⟩ : ∃ u : AE D, u = 1 - f := ⟨_, rfl⟩
  have huf : u * f = 0 := by rw [hu, sub_mul, one_mul, hff, sub_self]
  have hus : ∀ x : k, u * p.sec x = 0 := by intro x; rw [← hf' x, ← mul_assoc, huf, zero_mul]
  have hucs : ∀ x : k, u * cA D (p.sec x) = 0 := by intro x; rw [← hcf' x, ← mul_assoc, huf, zero_mul]
  have huu : u * u = u := by nth_rewrite 2 [hu]; rw [mul_sub, mul_one, huf, sub_zero]
  have hcu : cA D u = u := by
    rw [hu, hfdef, map_sub, map_one, map_add, hcc, add_comm]
  refine ⟨u + p.sec c₀ + cA D (p.sec c₀⁻¹), ⟨?_, ?_⟩, ?_⟩
  · have hconj : cA D (u + p.sec c₀ + cA D (p.sec c₀⁻¹)) = u + cA D (p.sec c₀) + p.sec c₀⁻¹ := by
      rw [map_add, map_add, hcu, hcc]
    show _ * cA D _ = 1
    rw [hconj]
    have e1 : p.sec c₀ * p.sec c₀⁻¹ = p.e := by rw [← sec_mul p, mul_inv_cancel₀ hc₀, he1]
    have e2 : cA D (p.sec c₀⁻¹) * cA D (p.sec c₀) = cA D p.e := by
      rw [← map_mul (cA D), ← sec_mul p, inv_mul_cancel₀ hc₀, he1]
    have s1 : p.sec c₀ * u = 0 := by rw [mul_comm (p.sec c₀) u]; exact hus _
    have s2 : cA D (p.sec c₀⁻¹) * u = 0 := by rw [mul_comm (cA D (p.sec c₀⁻¹)) u]; exact hucs _
    have s3 : cA D (p.sec c₀⁻¹) * p.sec c₀⁻¹ = 0 := by rw [mul_comm (cA D (p.sec c₀⁻¹)) (p.sec c₀⁻¹)]; exact hsc _ _
    have s4 : p.sec c₀ * cA D (p.sec c₀) = 0 := hsc _ _
    have expand : (u + p.sec c₀ + cA D (p.sec c₀⁻¹)) * (u + cA D (p.sec c₀) + p.sec c₀⁻¹)
        = u * u + u * cA D (p.sec c₀) + u * p.sec c₀⁻¹ + p.sec c₀ * u + p.sec c₀ * cA D (p.sec c₀)
          + p.sec c₀ * p.sec c₀⁻¹ + cA D (p.sec c₀⁻¹) * u + cA D (p.sec c₀⁻¹) * cA D (p.sec c₀)
          + cA D (p.sec c₀⁻¹) * p.sec c₀⁻¹ := by ring
    rw [expand, huu, hucs, hus, s1, s4, e1, s2, e2, s3, hu, hfdef]
    ring
  · have : u + p.sec c₀ + cA D (p.sec c₀⁻¹) - 1 = -f + p.sec c₀ + cA D (p.sec c₀⁻¹) := by rw [hu]; ring
    rw [this]
    refine add_mem (add_mem (neg_mem hfm) (sec_mem_idAt p _)) (csec_mem_idAt (p := p) _)
  · rw [map_add, map_add, hprc, add_zero, hu, hfdef, map_sub, map_one, map_add, ← he1, hprc, p.pr_sec, p.pr_sec]
    ring

end GlobalTheory.Core.Mi.LatMatch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReductionIffPatternStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reduction_iff_pattern : ∀ (D : D7) (u : D.what₂.Word) (d : GlobalTheory.SeeSaw.Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (PP : Formalism.L2.DIV.Pl D.host.E) (G : GlobalTheory.LocMod.GAt d τ PP) (g : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP)), (∃ x, G.Red x g) ↔ GlobalTheory.SymRes.IsPat D.R.rS D.R.k g := by
  first | exact @GlobalTheory.SymRes.exists_red_iff | exact GlobalTheory.SymRes.exists_red_iff | (intros; apply GlobalTheory.SymRes.exists_red_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRowFormPrescribedValuesClassRepresentative
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.PerIn

theorem exists_Mt_of_rep_values : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Formalism.BasicNotions.Ranks} {I : GlobalTheory.Mem.Col2.ChainIn E K ι R} (Q : GlobalTheory.Mem.Col2.PerIn I) (emb : ι → E →+* K) (σ : K →+* ℂ), (∀ b, Q.H b = ⊤) → ∀ (w : Q.S'.Cl → Formalism.L2.DIV.Pol ℂ ι (R.N R.m - 1)), (∀ c, w c ∈ Formalism.L2.DIV.VV ℂ Q.sgT) → (∀ c (s : Q.S'.Stab c), w c = (σ (Q.S'.chr c.1 s.1 : K))⁻¹ • Formalism.L2.DIV.rhoP Q.sgT (Formalism.L2.DIV.embGL (Formalism.L2.Col.embAt σ emb) (Q.S'.gam c.1 s.1)) (w c)) → ∃ F : Q.Mt emb σ, ∀ c, F.1 c.1 (Q.S'.rep c) = w c := by
  intro E K ι _ _ _ _ _ _ _ R I Q emb σ _hH w hw hinv
  classical
  let φ : ∀ b, Q.S'.G b → Pol ℂ ι (R.N R.m - 1) → Pol ℂ ι (R.N R.m - 1) := fun b g x =>
    (σ (Q.S'.chr b g : K))⁻¹ • rhoP Q.sgT (embGL (Formalism.L2.Col.embAt σ emb) (Q.S'.gam b g)) x
  have φmul : ∀ b (g h : Q.S'.G b) x, φ b (g * h) x = φ b g (φ b h x) := by
    intro b g h x
    simp only [φ, map_mul, Units.val_mul, mul_inv, Module.End.mul_apply, map_smul, smul_smul]
  have hinv' : ∀ c (s : Q.S'.G c.1), s • Q.S'.rep c = Q.S'.rep c → w c = φ c.1 s (w c) :=
    fun c s hs => hinv c ⟨s, hs⟩
  let F : ∀ b, Q.S'.D b → Pol ℂ ι (R.N R.m - 1) := fun b d => φ b (Q.S'.mv b d) (w (Q.S'.cl b d))
  have hcl : ∀ b (g : Q.S'.G b) (d : Q.S'.D b), Q.S'.cl b (g • d) = Q.S'.cl b d := fun b g d =>
    Sigma.ext rfl (heq_of_eq (Quotient.sound (MulAction.mem_orbit d g)))
  have hlaw : ∀ b (g : Q.S'.G b) d, F b (g • d) = φ b g (F b d) := by
    intro b g d
    set c := Q.S'.cl b d with hc
    have hrep : Q.S'.rep (Q.S'.cl b (g • d)) = Q.S'.rep c :=
      congrArg (Q.S'.rp b) (Quotient.sound (MulAction.mem_orbit d g))
    have h1 : Q.S'.mv b (g • d) • Q.S'.rep c = g • d := by
      convert Q.S'.mv_smul b (g • d) using 2; exact hrep.symm
    have h2 := Q.S'.mv_smul b d
    have hs : ((g * Q.S'.mv b d)⁻¹ * Q.S'.mv b (g • d)) • Q.S'.rep c = Q.S'.rep c := by
      rw [mul_smul, h1, _root_.mul_inv_rev, mul_smul, inv_smul_smul, inv_smul_eq_iff, h2]
    have hw := hinv' c _ hs
    show φ b (Q.S'.mv b (g • d)) (w (Q.S'.cl b (g • d))) = φ b g (φ b (Q.S'.mv b d) (w c))
    rw [hcl, ← φmul]
    conv_rhs => rw [hw, ← φmul, mul_inv_cancel_left]
  refine ⟨⟨F, fun b d => ⟨?_, fun g _ => hlaw b g d⟩⟩, ?_⟩
  · exact Submodule.smul_mem _ _ (polyAction_mem_VV _ _ (hw _))
  · rintro ⟨b, q⟩
    have hq : Q.S'.cl b (Q.S'.rep ⟨b, q⟩) = ⟨b, q⟩ := Sigma.ext rfl (heq_of_eq (Q.S'.rp_spec b q))
    have hr : Q.S'.rep (Q.S'.cl b (Q.S'.rep ⟨b, q⟩)) = Q.S'.rep ⟨b, q⟩ := congrArg (Q.S'.rp b) (Q.S'.rp_spec b q)
    have h1 : Q.S'.mv b (Q.S'.rep ⟨b, q⟩) • Q.S'.rep ⟨b, q⟩ = Q.S'.rep ⟨b, q⟩ := by
      convert Q.S'.mv_smul b (Q.S'.rep ⟨b, q⟩) using 2; exact hr.symm
    show φ b (Q.S'.mv b (Q.S'.rep ⟨b, q⟩)) (w (Q.S'.cl b (Q.S'.rep ⟨b, q⟩))) = w ⟨b, q⟩
    rw [hq]
    exact (hinv' ⟨b, q⟩ _ h1).symm

end GlobalTheory.Mem.Col2.PerIn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLineLatticeTraceAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

open Formalism.MainNotions.StandardLattice

namespace GlobalTheory.Core.Mi.LineSD

variable {D : D7}

theorem mul_mem_intAt {v : GlobalTheory.FinPl.Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_right _ _ ha.1, by rw [map_mul]; exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE ha.2 hb.2⟩

theorem one_mem_intAf : (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ∈ intAf D.host.F := fun w => by
  rw [map_one]; exact one_mem _

theorem incA_mem_intAE (x : 𝓞 D.host.E) : finPart D (incA D (x : D.host.E)) ∈ intAE D :=
  AddSubgroup.subset_closure ⟨1, one_mem_intAf, x, rfl⟩

theorem mul_incA_mem {v : GlobalTheory.FinPl.Pl D} {a : AE D} (ha : a ∈ intAt D (· = v)) (x : 𝓞 D.host.E) :
    a * incA D (x : D.host.E) ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_right _ _ ha.1, by
    rw [map_mul]; exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE ha.2 (incA_mem_intAE x)⟩

theorem cA_mem_intAt {v : GlobalTheory.FinPl.Pl D} {a : AE D} (ha : a ∈ intAt D (· = v)) : cA D a ∈ intAt D (· = v) := by
  refine ⟨?_, (GlobalTheory.FinPl.FrameLat.cA_int_iff a).2 ha.2⟩
  have h := (GlobalTheory.FinPlLoc.mem_idAt_iff _ a).1 ha.1
  rw [GlobalTheory.FinPlLoc.mem_idAt_iff, ← GlobalTheory.FinPlLoc.cA_idem, ← map_mul, h]

theorem unit_at {v : GlobalTheory.FinPl.Pl D} {T : ℕ} (hT : (T : 𝓞 D.host.F) ∉ v.asIdeal) :
    GlobalTheory.FinPlLoc.idem D (· = v) * incA D ((T : D.host.E)⁻¹) ∈ intAt D (· = v) := by
  refine ⟨Ideal.mul_mem_right _ _ (GlobalTheory.FinPlLoc.idem_mem_idAt _), ?_⟩
  have hc : ((T : D.host.E)⁻¹) = algebraMap D.host.F D.host.E ((T : D.host.F)⁻¹) := by simp
  have e : finPart D (GlobalTheory.FinPlLoc.idem D (· = v) * incA D ((T : D.host.E)⁻¹)) =
      ((T : D.host.F)⁻¹ • GlobalTheory.FinPlLoc.ePl D (· = v)) ⊗ₜ[D.host.F] (1 : D.host.E) := by
    rw [map_mul, GlobalTheory.FinPlLoc.idem, GlobalTheory.FinPlLoc.finPart_pair]
    show (GlobalTheory.FinPlLoc.ePl D (· = v) ⊗ₜ[D.host.F] (1 : D.host.E)) *
      ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] ((T : D.host.E)⁻¹)) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, hc, Algebra.algebraMap_eq_smul_one,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  rw [e]
  refine AddSubgroup.subset_closure ⟨(T : D.host.F)⁻¹ • GlobalTheory.FinPlLoc.ePl D (· = v), fun w => ?_, (1 : 𝓞 D.host.E), ?_⟩
  swap
  · rfl
  rw [Algebra.smul_def, map_mul, AlgHom.commutes, GlobalTheory.FinPlLoc.evalV_ePl]
  by_cases hw : w = v
  · subst hw
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, if_pos rfl, mul_one]
    show Valued.v (((T : D.host.F)⁻¹ : D.host.F) : w.adicCompletion D.host.F) ≤ 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀]
    have h1 : w.valuation D.host.F (T : D.host.F) = 1 := by
      have := HeightOneSpectrum.valuation_of_algebraMap (K := D.host.F) w (T : 𝓞 D.host.F)
      rw [HeightOneSpectrum.intValuation_eq_one_iff.2 hT] at this
      simpa using this
    rw [h1, inv_one]
  · rw [if_neg hw, mul_zero]; exact zero_mem _

def traceLine {S A L : HSp D} (o : OrthDec S A L) (M' : Lat S) (v : GlobalTheory.FinPl.Pl D) :
    AddSubgroup (Fin L.rank → AE D) where
  carrier := {l | (∀ i, l i ∈ idAt D (· = v)) ∧ o.jB *ᵥ l ∈ latV S M' (· = v)}
  add_mem' := fun {a b} ha hb => ⟨fun i => add_mem (ha.1 i) (hb.1 i), by
    show o.jB *ᵥ (a + b) ∈ _
    rw [mulVec_add]; exact add_mem ha.2 hb.2⟩
  zero_mem' := ⟨fun i => zero_mem _, by
    show o.jB *ᵥ 0 ∈ _
    rw [mulVec_zero]; exact zero_mem _⟩
  neg_mem' := fun {a} ha => ⟨fun i => neg_mem (ha.1 i), by
    show o.jB *ᵥ (-a) ∈ _
    rw [mulVec_neg]; exact neg_mem ha.2⟩

theorem exists_isSDAt_line : ∀ (D : D7) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (M' : Lat S) (μ : D.host.E) (T : ℕ) (v : GlobalTheory.FinPl.Pl D), IsLineVec L ζ → μ ≠ 0 → LineAt (vecB o ζ) μ M' v → star ζ ⬝ᵥ L.gram *ᵥ ζ = -(μ * star μ * (T : D.host.E)) → (T : 𝓞 D.host.F) ∉ v.asIdeal → ∃ Λ' : AddSubgroup (Fin L.rank → AE D), GlobalTheory.IwaPlace.IsSDAt L v Λ' ∧ ∀ l : Fin L.rank → AE D, (∀ i, l i ∈ idAt D (· = v)) → (l ∈ Λ' ↔ o.jB *ᵥ l ∈ latV S M' (· = v)) := by
  intro D S A L o ζ M' μ T v hζ hμ hline hgram hT
  obtain ⟨hr, hne⟩ := hζ
  obtain ⟨i₀, hall⟩ : ∃ i₀ : Fin L.rank, ∀ i, i = i₀ :=
    ⟨⟨0, by omega⟩, fun i => Fin.ext (by have := i.2; simp only; omega)⟩
  have hs : ∀ {M : Type} [AddCommMonoid M] (f : Fin L.rank → M), ∑ i, f i = f i₀ := fun f =>
    Fintype.sum_eq_single _ fun i hi => absurd (hall i) hi
  have hdot : star ζ ⬝ᵥ L.gram *ᵥ ζ = star (ζ i₀) * L.gram i₀ i₀ * ζ i₀ := by
    simp only [dotProduct, mulVec, hs, Pi.star_apply]; ring
  have hz0 : ζ i₀ ≠ 0 := by
    intro h; apply hne; rw [hdot, h, mul_zero]
  have hsz : star (ζ i₀) ≠ 0 := star_ne_zero.2 hz0
  have hT0 : (T : D.host.E) ≠ 0 := by
    have : T ≠ 0 := by rintro rfl; exact hT (by simp)
    exact_mod_cast this
  have hq : star (ζ i₀) * L.gram i₀ i₀ * ζ i₀ = -(μ * star μ * (T : D.host.E)) := by rw [← hdot, hgram]
  have hjB : ∀ l : Fin L.rank → AE D, o.jB *ᵥ l = (l i₀ * incA D (ζ i₀)⁻¹) • ratV (vecB o ζ) := by
    intro l; funext r
    simp only [OrthDec.jB, rat, vecB, ratV, mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul, hs]
    rw [map_mul]
    have h1 : incA D (ζ i₀)⁻¹ * incA D (ζ i₀) = 1 := by rw [← map_mul, inv_mul_cancel₀ hz0, map_one]
    linear_combination (-(incA D (o.iB r i₀) * l i₀)) * h1
  have hK : ∀ l : Fin L.rank → AE D, (∀ i, l i ∈ idAt D (· = v)) →
      (o.jB *ᵥ l ∈ latV S M' (· = v) ↔ l i₀ * incA D (μ / ζ i₀) ∈ intAt D (· = v)) := by
    intro l hl
    rw [hjB, hline _ (Ideal.mul_mem_right _ _ (hl i₀))]
    have : incA D μ * (l i₀ * incA D (ζ i₀)⁻¹) = l i₀ * incA D (μ / ζ i₀) := by
      rw [div_eq_mul_inv, map_mul]; ring
    rw [this]
  let Λ' := traceLine o M' v
  have hmem : ∀ l, l ∈ Λ' ↔ (∀ i, l i ∈ idAt D (· = v)) ∧ o.jB *ᵥ l ∈ latV S M' (· = v) := fun l => Iff.rfl
  have hΛ : ∀ x, x ∈ Λ' ↔ (∀ i, x i ∈ idAt D (· = v)) ∧ x i₀ * incA D (μ / ζ i₀) ∈ intAt D (· = v) :=
    fun x => (hmem x).trans (and_congr_right fun hx => hK x hx)
  refine ⟨Λ', ⟨fun y hy => hy.1, ?_, ?_⟩, fun l hl => by rw [hmem]; exact ⟨fun h => h.2, fun h => ⟨hl, h⟩⟩⟩
  · obtain ⟨y, hy0, hyint⟩ :=
      exists_integral_multiples ℤ ℚ (L := D.host.E) {μ / ζ i₀}
    replace hyint := hyint _ (Finset.mem_singleton_self _)
    have hn : IsIntegral ℤ ((y.natAbs : D.host.E) * (μ / ζ i₀)) := by
      rcases Int.natAbs_eq y with h | h
      · rw [h, zsmul_eq_mul, Int.cast_natCast] at hyint; exact hyint
      · rw [h, neg_smul, zsmul_eq_mul, Int.cast_natCast] at hyint; simpa using hyint.neg
    refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, fun x hx => ?_⟩
    refine (hΛ _).2 ⟨fun i => ?_, ?_⟩
    · rw [Pi.smul_apply, smul_eq_mul]; exact Ideal.mul_mem_left _ _ (hx i).1
    · have : ((y.natAbs : AE D) • x) i₀ * incA D (μ / ζ i₀) =
          x i₀ * incA D ((y.natAbs : D.host.E) * (μ / ζ i₀)) := by
        rw [Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]; ring
      rw [this]; exact mul_incA_mem (hx i₀) ⟨_, hn⟩
  · intro y hy
    have hherm : ∀ x : Fin L.rank → AE D, GlobalTheory.IwaPlace.hermAt L y x = cA D (x i₀) * incA D (L.gram i₀ i₀) * y i₀ := by
      intro x; simp only [GlobalTheory.IwaPlace.hermAt, hs, gA, rat, Matrix.map_apply]
    have hG : L.gram i₀ i₀ = star (μ / ζ i₀) * (-(T : D.host.E)) * (μ / ζ i₀) := by
      have h1 : L.gram i₀ i₀ = -(μ * star μ * (T : D.host.E)) / (star (ζ i₀) * ζ i₀) := by
        rw [eq_div_iff (mul_ne_zero hsz hz0)]; linear_combination hq
      rw [h1, div_eq_mul_inv μ, star_mul', star_inv₀]
      field_simp
    have hid : ∀ a : AE D, cA D a * incA D (L.gram i₀ i₀) * y i₀ =
        cA D (a * incA D (μ / ζ i₀)) * (y i₀ * incA D (μ / ζ i₀)) * incA D (-(T : D.host.E)) := by
      intro a
      rw [hG]; simp only [map_mul, GlobalTheory.FinPl.FrameLat.cA_incA]; ring
    have hay : y i₀ * incA D (μ / ζ i₀) ∈ idAt D (· = v) := Ideal.mul_mem_right _ _ (hy i₀)
    have he : GlobalTheory.FinPlLoc.idem D (· = v) * incA D (ζ i₀ / μ) * incA D (μ / ζ i₀) = GlobalTheory.FinPlLoc.idem D (· = v) := by
      rw [mul_assoc, ← map_mul, show ζ i₀ / μ * (μ / ζ i₀) = 1 by field_simp, map_one, mul_one]
    constructor
    · intro hyΛ x hx
      obtain ⟨-, hyK⟩ := (hΛ y).1 hyΛ
      obtain ⟨-, hxK⟩ := (hΛ x).1 hx
      rw [hherm, hid]
      have := mul_incA_mem (mul_mem_intAt (cA_mem_intAt hxK) hyK) (-(T : 𝓞 D.host.E))
      simpa using this
    · intro h
      refine (hΛ y).2 ⟨hy, ?_⟩
      have hx₁ : (fun _ => GlobalTheory.FinPlLoc.idem D (· = v) * incA D (ζ i₀ / μ) : Fin L.rank → AE D) ∈ Λ' := by
        refine (hΛ _).2 ⟨fun i => Ideal.mul_mem_right _ _ (GlobalTheory.FinPlLoc.idem_mem_idAt _), ?_⟩
        show GlobalTheory.FinPlLoc.idem D (· = v) * incA D (ζ i₀ / μ) * incA D (μ / ζ i₀) ∈ _
        rw [he]; exact GlobalTheory.FinPlLoc.idem_mem_intAt _
      have h1 := h _ hx₁
      rw [hherm, hid] at h1
      rw [he, GlobalTheory.FinPlLoc.cA_idem, (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 hay] at h1
      have h2 := mul_incA_mem (mul_mem_intAt h1 (unit_at hT)) (-1 : 𝓞 D.host.E)
      have hT' : incA D (-(T : D.host.E)) * incA D ((T : D.host.E)⁻¹) * incA D (((-1 : 𝓞 D.host.E)) : D.host.E) = 1 := by
        rw [← map_mul, ← map_mul]; push_cast; rw [neg_mul, mul_inv_cancel₀ hT0]; simp
      have hay' := (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 hay
      have e2 : y i₀ * incA D (μ / ζ i₀) * incA D (-(T : D.host.E)) *
          (GlobalTheory.FinPlLoc.idem D (· = v) * incA D ((T : D.host.E)⁻¹)) * incA D (((-1 : 𝓞 D.host.E)) : D.host.E) =
          y i₀ * incA D (μ / ζ i₀) := by
        linear_combination (GlobalTheory.FinPlLoc.idem D (· = v) * (y i₀ * incA D (μ / ζ i₀))) * hT' + hay'
      rw [e2] at h2; exact h2

end GlobalTheory.Core.Mi.LineSD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationsDistinctSplitPlacesCollectStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergCombinations_distinct_split_places_collect : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : GlobalTheory.FinPl.Lat S) (M' : GlobalTheory.FinPl.Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (L : Fin n → GlobalTheory.SeeSaw.LocPl ψ S T M M'), (Function.Injective fun i => (L i).q.v) → ∀ F, (List.finRange n).foldr (fun i g => comb ψ S T (L i).e (comb ψ S T (L i).o g)) F = (List.finRange n).foldr (fun i g => comb ψ S T (L i).e g) ((List.finRange n).foldr (fun i g => comb ψ S T (L i).o g) F) := by
  first | exact @GlobalTheory.CollectComb.main | exact GlobalTheory.CollectComb.main | (intros; apply GlobalTheory.CollectComb.main <;> assumption)
end

