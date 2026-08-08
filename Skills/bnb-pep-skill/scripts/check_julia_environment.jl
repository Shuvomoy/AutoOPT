#!/usr/bin/env julia

# Environment check for generated Stage 1/2 BnB-PEP workflows.
#
# Version floors:
# - JuMP >= 1.15 is REQUIRED: generated Stage 2 models build cubic/trilinear
#   expressions through JuMP's nonlinear-expression interface
#   (ScalarNonlinearFunction), introduced in JuMP 1.15. Older JuMP versions
#   fail at model-build time.
# - Julia >= 1.10 and Ipopt >= 1.4 are recommended minimums (warnings only).

hard_required_packages = [
    "JuMP",
    "OffsetArrays",
    "Clarabel",
    "Ipopt",
]

recommended_packages = [
    "MosekTools",
    "Mosek",
    "KNITRO",
]

const JUMP_REQUIRED_VERSION = v"1.15.0"
const JULIA_RECOMMENDED_VERSION = v"1.10.0"
const IPOPT_RECOMMENDED_VERSION = v"1.4.0"

function package_version(pkg)
    path = Base.find_package(pkg)
    path === nothing && return nothing
    project_file = joinpath(dirname(dirname(path)), "Project.toml")
    isfile(project_file) || return nothing
    for line in eachline(project_file)
        m = match(r"^version\s*=\s*\"([^\"]+)\"", line)
        if m !== nothing
            return try
                VersionNumber(m.captures[1])
            catch
                nothing
            end
        end
    end
    return nothing
end

println("Julia version: ", VERSION)
if VERSION < JULIA_RECOMMENDED_VERSION
    println("WARNING: Julia ", JULIA_RECOMMENDED_VERSION,
            " or newer is recommended for generated BnB-PEP workflows.")
end
println("Checking BnB-PEP skill package availability:")

function check_package_group(label, packages)
    println()
    println(label, ":")
    missing_pkgs = String[]
    for pkg in packages
        path = Base.find_package(pkg)
        if path === nothing
            println("MISSING  ", pkg)
            push!(missing_pkgs, pkg)
        else
            ver = package_version(pkg)
            version_text = ver === nothing ? "version unknown" : string("v", ver)
            println("FOUND    ", pkg, " (", version_text, ") => ", path)
        end
    end
    return missing_pkgs
end

missing_required = check_package_group("Hard required packages", hard_required_packages)
missing_recommended = check_package_group("Recommended solver packages", recommended_packages)

println()

jump_version = "JuMP" in missing_required ? nothing : package_version("JuMP")
jump_version_failed = false
if !("JuMP" in missing_required)
    if jump_version === nothing
        println("WARNING: JuMP was found but its version could not be determined; ",
                "generated Stage 2 models require JuMP >= ", JUMP_REQUIRED_VERSION, ".")
    elseif jump_version < JUMP_REQUIRED_VERSION
        jump_version_failed = true
        println("JuMP v", jump_version, " is older than the required v",
                JUMP_REQUIRED_VERSION,
                ": generated Stage 2 models build cubic terms through JuMP's ",
                "nonlinear-expression interface (ScalarNonlinearFunction) and ",
                "will fail to build on this version.")
    end
end

ipopt_version = "Ipopt" in missing_required ? nothing : package_version("Ipopt")
if ipopt_version !== nothing && ipopt_version < IPOPT_RECOMMENDED_VERSION
    println("WARNING: Ipopt v", ipopt_version, " is older than the recommended v",
            IPOPT_RECOMMENDED_VERSION, ".")
end

if isempty(missing_required) && !jump_version_failed
    println("Hard required Stage 1/2 packages are discoverable: JuMP, OffsetArrays, Clarabel, and Ipopt.")
    if !isempty(missing_recommended)
        println("Recommended packages missing: ", join(missing_recommended, ", "))
        println("MosekTools/Mosek and KNITRO are recommended accelerators but are not required.")
    else
        println("Recommended solver packages are also discoverable: MosekTools, Mosek, and KNITRO.")
    end
    println("Solver licenses and runtime behavior still need smoke-test confirmation.")
    exit(0)
else
    if !isempty(missing_required)
        println("Missing required packages: ", join(missing_required, ", "))
    end
    if jump_version_failed
        println("JuMP is below the required version floor v", JUMP_REQUIRED_VERSION, ".")
    end
    if !isempty(missing_recommended)
        println("Recommended packages missing: ", join(missing_recommended, ", "))
        println("MosekTools/Mosek and KNITRO are recommended but not required.")
    end
    println("Install or activate a Julia environment containing JuMP >= ",
            JUMP_REQUIRED_VERSION,
            ", OffsetArrays, Clarabel, and Ipopt before running generated BnB-PEP smoke tests.")
    exit(1)
end
