/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Meta.Basic
import PhysLean.Meta.TODO.Basic
import Mathlib.Lean.CoreM
import PhysLean.Meta.Informal.Post
/-!

# Turning TODOs into YAML

-/

open Lean System Meta PhysLean


/-!

## PhysLean categories.

To be moved.

-/
inductive PhysLeanCategory
  | ClassicalMechanics
  | CondensedMatter
  | Cosmology
  | Elctromagnetism
  | Mathematics
  | Meta
  | Optics
  | Particles
  | QFT
  | QuantumMechanics
  | Relativity
  | StatisticalMechanics
  | Thermodynamics
  | Other

def PhysLeanCategory.string :  PhysLeanCategory → String
  | ClassicalMechanics => "Classical Mechanics"
  | CondensedMatter => "Condensed Matter"
  | Cosmology => "Cosmology"
  | Elctromagnetism => "Electromagnetism"
  | Mathematics => "Mathematics"
  | Meta => "Meta"
  | Optics => "Optics"
  | Particles => "Particles"
  | QFT => "QFT"
  | QuantumMechanics => "Quantum Mechanics"
  | Relativity => "Relativity"
  | StatisticalMechanics => "Statistical Mechanics"
  | Thermodynamics => "Thermodynamics"
  | Other => "Other"

instance : ToString PhysLeanCategory where
  toString := PhysLeanCategory.string

def PhysLeanCategory.ofFileName (n : Name) : PhysLeanCategory :=
  if n.toString.startsWith "PhysLean.ClassicalMechanics"  then
    PhysLeanCategory.ClassicalMechanics
  else if n.toString.startsWith "PhysLean.CondensedMatter" then
    PhysLeanCategory.CondensedMatter
  else if n.toString.startsWith "PhysLean.Cosmology" then
    PhysLeanCategory.Cosmology
  else if n.toString.startsWith "PhysLean.Electromagnetism" then
    PhysLeanCategory.Elctromagnetism
  else if n.toString.startsWith "PhysLean.Mathematics" then
    PhysLeanCategory.Mathematics
  else if n.toString.startsWith "PhysLean.Meta" then
    PhysLeanCategory.Meta
  else if n.toString.startsWith "PhysLean.Optics" then
    PhysLeanCategory.Optics
  else if n.toString.startsWith "PhysLean.Particles" then
    PhysLeanCategory.Particles
  else if n.toString.startsWith "PhysLean.QFT" then
    PhysLeanCategory.QFT
  else if n.toString.startsWith "PhysLean.QuantumMechanics" then
    PhysLeanCategory.QuantumMechanics
  else if n.toString.startsWith "PhysLean.Relativity" then
    PhysLeanCategory.Relativity
  else if n.toString.startsWith "PhysLean.StatisticalMechanics" then
    PhysLeanCategory.StatisticalMechanics
  else if n.toString.startsWith "PhysLean.Thermodynamics" then
    PhysLeanCategory.Thermodynamics
  else
    PhysLeanCategory.Other

/-########################-/

structure FullTODOInfo where
  content : String
  fileName : Name
  line : Nat
  isInformalDef : Bool
  isInformalLemma : Bool
  category : PhysLeanCategory

def FullTODOInfo.ofTODO (t : todoInfo) : FullTODOInfo :=
  {content := t.content, fileName := t.fileName, line := t.line,
   isInformalDef := false, isInformalLemma := false, category := PhysLeanCategory.ofFileName t.fileName}

unsafe def getTodoInfo : MetaM (Array FullTODOInfo) := do
  let env ← getEnv
  let todoInfo := (todoExtension.getState env)
  -- pure (todoInfo.qsort (fun x y => x.fileName.toString < y.fileName.toString)).toList
  pure (todoInfo.map FullTODOInfo.ofTODO)

def informalTODO (x : ConstantInfo) : CoreM FullTODOInfo := do
  let name := x.name
  let lineNo ← Name.lineNumber name
  let docString ← Name.getDocString name
  let file ← Name.fileName name
  let isInformalDef := Informal.isInformalDef x
  let isInformalLemma := Informal.isInformalLemma x
  let category := PhysLeanCategory.ofFileName file
  return {content := docString, fileName := file, line := lineNo,
          isInformalDef := isInformalDef, isInformalLemma := isInformalLemma, category := category}

def allInformalTODO : CoreM (Array FullTODOInfo) := do
  let x ← AllInformal
  x.mapM informalTODO

def FullTODOInfo.toYAML (todo : FullTODOInfo) : MetaM String := do
  let content := todo.content
  let contentIndent := content.replace "\n" "\n    "
  return s!"
- file: {todo.fileName}
  githubLink: {Name.toGitHubLink todo.fileName todo.line}
  line: {todo.line}
  isInformalDef: {todo.isInformalDef}
  isInformalLemma: {todo.isInformalLemma}
  category: {todo.category}
  content: |
    {contentIndent}"

unsafe def allTODOs : MetaM (List FullTODOInfo) := do
  let todos ← getTodoInfo
  let informalTODOs ← allInformalTODO
  let all := todos ++ informalTODOs
  return  (all.qsort (fun x y => x.fileName.toString < y.fileName.toString)).toList

unsafe def todosToYAML : MetaM String := do
  let todos ← allTODOs
  let todosYAML ← todos.mapM FullTODOInfo.toYAML
  return String.intercalate "\n" todosYAML

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  println! "Generating TODO list."
  let ymlString ← CoreM.withImportModules #[`PhysLean] (todosToYAML).run'
  println! ymlString
  let fileOut : System.FilePath := {toString := "./docs/_data/TODO.yml"}
  if "mkFile" ∈ args then
    IO.println (s!"TODOList file made.")
    IO.FS.writeFile fileOut ymlString
  pure 0
