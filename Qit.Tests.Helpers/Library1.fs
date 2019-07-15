namespace Qit.Tests.Helpers

open System

type TypeWithFields = 
    val mutable A : DateTime
    new(d) = {A = d}


type TypeWithFields2 = 
    val A : DateTime
    new(d) = {A = d}

    
type TypeWithFields3 = 
    val A : DateTime []
    new(d) = {A = [|d|]}

type TypeWithFields4 = 
    val mutable A : DateTime []
    new(d) = {A = [|d|]}

