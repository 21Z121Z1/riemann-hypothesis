import Lean.LibrarySuggestions.Basic
import Lean.Elab.Command

-- bundled from BuildAid.D1
section
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "CompanionTheory"
end

-- bundled from BuildAid.D2
section
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "CrystallineSemistableComparison"
end

-- bundled from BuildAid.D3
section
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "GlobalTheory"
end

-- bundled from BuildAid.D4
section
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PositivityTheory"
end

-- bundled from BuildAid.D5
section
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "UpperTheory"
end

