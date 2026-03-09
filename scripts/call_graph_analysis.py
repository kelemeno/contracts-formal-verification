#!/usr/bin/env python3
"""
Extracts call graphs from Yul files and analyzes generated Lean file imports.
Usage: python3 call_graph_analysis.py
"""

import re
import os
import sys

BASE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

def extract_call_graph(filepath):
    with open(filepath) as f:
        lines = f.readlines()

    # Find all function definitions with their line ranges
    func_defs = []
    func_pattern = re.compile(r'^\s*function\s+(\w+)\s*\(')

    for i, line in enumerate(lines):
        m = func_pattern.match(line)
        if m:
            func_defs.append((m.group(1), i+1))  # name, 1-based line number

    # Build a set of known function names
    known_funcs = set(name for name, _ in func_defs)

    # For each function, find its body and extract calls
    call_graph = {}
    for idx, (name, start_line) in enumerate(func_defs):
        # Find end of function by tracking braces
        start_idx = start_line - 1
        brace_count = 0
        end_idx = start_idx
        started = False
        for i in range(start_idx, len(lines)):
            # Strip comments and strings before counting braces
            clean_line = lines[i]
            ci = clean_line.find('///')
            if ci >= 0:
                clean_line = clean_line[:ci]
            clean_line = re.sub(r'/\*\*.*?\*/', '', clean_line)
            clean_line = re.sub(r'"[^"]*"', '""', clean_line)
            brace_count += clean_line.count('{') - clean_line.count('}')
            if clean_line.count('{') > 0:
                started = True
            if started and brace_count <= 0:
                end_idx = i
                break

        # Extract function calls from body (strip comments and strings first)
        body_lines = lines[start_idx:end_idx+1]
        # Remove /// comments and quoted strings that may contain braces
        clean_lines = []
        for bl in body_lines:
            # Strip /// comments
            comment_idx = bl.find('///')
            if comment_idx >= 0:
                bl = bl[:comment_idx]
            # Strip /** ... */ comments
            bl = re.sub(r'/\*\*.*?\*/', '', bl)
            # Strip quoted strings
            bl = re.sub(r'"[^"]*"', '""', bl)
            clean_lines.append(bl)
        body = ''.join(clean_lines)
        # Match function calls: word followed by (
        call_pattern = re.compile(r'\b(\w+)\s*\(')
        calls = set()
        for m in call_pattern.finditer(body):
            callee = m.group(1)
            if callee in known_funcs and callee != name:
                calls.add(callee)
        # Exclude keywords
        calls -= {'function', 'if', 'for', 'switch', 'let', 'case', 'default'}

        call_graph[name] = (start_line, sorted(calls))

    return call_graph, func_defs


def categorize_funcs(defs):
    categories = {
        'fun_': [],
        'modifier_': [],
        'external_fun_': [],
        'abi_decode': [],
        'abi_encode': [],
        'other': [],
    }
    prefixes = ['fun_', 'modifier_', 'external_fun_', 'abi_decode', 'abi_encode']
    for name, line in defs:
        matched = False
        for p in prefixes:
            if name.startswith(p):
                categories[p].append((name, line))
                matched = True
                break
        if not matched:
            categories['other'].append((name, line))
    return categories


def print_category(label, items, cg):
    print(f"\n--- {label} ---")
    for name, line in items:
        calls = cg[name][1]
        print(f"  L{line}: {name}")
        if calls:
            print(f"    calls: {', '.join(calls)}")


def analyze_lean_imports(contract_name):
    """Read _gen.lean files for fun_* functions and extract imports."""
    gen_dir = os.path.join(BASE, 'generated', contract_name, contract_name)
    if not os.path.isdir(gen_dir):
        print(f"  Directory not found: {gen_dir}")
        return

    # Find all fun_*_gen.lean files
    fun_gen_files = sorted([
        f for f in os.listdir(gen_dir)
        if f.startswith('fun_') and f.endswith('_gen.lean')
    ])

    print(f"\n--- Lean Import Analysis for {contract_name} fun_* functions ---")
    for fname in fun_gen_files:
        fpath = os.path.join(gen_dir, fname)
        func_name = fname.replace('_gen.lean', '')
        with open(fpath) as f:
            content = f.read()

        # Extract imports
        imports = re.findall(r'import\s+(\S+)', content)
        # Filter to only the contract's own imports
        relevant = [imp for imp in imports if contract_name in imp]
        # Extract just the function/module names
        called = []
        for imp in relevant:
            parts = imp.split('.')
            leaf = parts[-1] if parts else imp
            if leaf != func_name and leaf != 'Common':
                called.append(leaf)

        print(f"\n  {func_name}:")
        if called:
            for c in sorted(set(called)):
                print(f"    -> {c}")
        else:
            print(f"    (no function imports found)")


def analyze_generated_files(contract_name):
    """Categorize generated Lean files."""
    gen_dir = os.path.join(BASE, 'generated', contract_name, contract_name)
    common_dir = os.path.join(gen_dir, 'Common')

    if not os.path.isdir(gen_dir):
        print(f"  Directory not found: {gen_dir}")
        return

    # Get base files (exclude _gen.lean and _user.lean variants)
    all_files = [f for f in os.listdir(gen_dir) if f.endswith('.lean') and f != 'Common']
    base_files = sorted(set(
        f.replace('_gen.lean', '.lean').replace('_user.lean', '.lean')
        for f in all_files if f.endswith('.lean')
    ))
    # Deduplicate
    base_names = sorted(set(f.replace('.lean', '') for f in base_files))

    cats = {
        'fun_': [],
        'modifier_': [],
        'external_fun_': [],
        'abi_decode_': [],
        'abi_encode_': [],
        'cleanup_': [],
        'validator_': [],
        'panic_error_': [],
        'require_helper_': [],
        'mapping_index_access_': [],
        'read_from_storage_': [],
        'update_storage_': [],
        'write_to_memory_': [],
        'extract_from_storage_': [],
        'allocate_': [],
        'finalize_allocation': [],
        'constant_': [],
        'checked_': [],
        'other': [],
    }
    prefixes = [k for k in cats.keys() if k != 'other']

    for name in base_names:
        matched = False
        for p in prefixes:
            if name.startswith(p):
                cats[p].append(name)
                matched = True
                break
        if not matched:
            cats['other'].append(name)

    print(f"\n{'='*80}")
    print(f"GENERATED FILES CATEGORIZATION: {contract_name}")
    print(f"{'='*80}")
    for cat, items in cats.items():
        if items:
            print(f"\n  {cat} ({len(items)} files):")
            for item in items:
                print(f"    {item}")

    # Common dir
    if os.path.isdir(common_dir):
        common_files = [f for f in os.listdir(common_dir) if f.endswith('.lean')]
        common_base = sorted(set(
            f.replace('_gen.lean', '.lean').replace('_user.lean', '.lean')
            for f in common_files
        ))
        common_names = sorted(set(f.replace('.lean', '') for f in common_base))

        if_files = [n for n in common_names if n.startswith('if_')]
        for_files = [n for n in common_names if n.startswith('for_')]
        switch_files = [n for n in common_names if n.startswith('switch_')]
        other_common = [n for n in common_names if not any(n.startswith(p) for p in ['if_', 'for_', 'switch_'])]

        print(f"\n  Common/if_* ({len(if_files)} blocks)")
        print(f"  Common/for_* ({len(for_files)} blocks)")
        print(f"  Common/switch_* ({len(switch_files)} blocks)")
        if other_common:
            print(f"  Common/other: {other_common}")


def print_dispatch_chains(cg, defs):
    """Show external_fun -> modifier/fun_ dispatch chains, with full call details."""
    print("\n--- External Function Dispatch Chains ---")
    print("  (Shows which fun_/modifier_ each external_fun calls,")
    print("   and all calls for external_funs with no fun_/modifier_ callees)")
    for name, line in defs:
        if not name.startswith('external_fun_'):
            continue
        calls = cg[name][1]
        solidity_calls = [c for c in calls if c.startswith('fun_') or c.startswith('modifier_')]
        print(f"\n  {name} (L{line})")
        if solidity_calls:
            for sc in solidity_calls:
                print(f"    -> {sc}")
                if sc.startswith('modifier_'):
                    mod_calls = cg[sc][1]
                    mod_sol = [c for c in mod_calls if c.startswith('fun_') or c.startswith('modifier_')]
                    for ms in mod_sol:
                        print(f"       -> {ms}")
                        if ms.startswith('modifier_'):
                            inner = cg[ms][1]
                            inner_sol = [c for c in inner if c.startswith('fun_')]
                            for ic in inner_sol:
                                print(f"          -> {ic}")
        else:
            print(f"    all calls: {', '.join(calls) if calls else '(none - pure getter/setter)'}")


def print_modifier_details(cg, defs):
    """Show full call lists for modifiers."""
    print("\n--- Modifier Full Call Lists ---")
    for name, line in defs:
        if name.startswith('modifier_'):
            print(f"\n  {name} (L{line})")
            print(f"    all calls: {', '.join(cg[name][1])}")


def main():
    print("=" * 100)
    print("L1NULLIFIER.YUL - CALL GRAPH")
    print("=" * 100)

    cg, defs = extract_call_graph(os.path.join(BASE, 'yul', 'L1Nullifier.yul'))
    cats = categorize_funcs(defs)

    print_category("Solidity Functions (fun_*)", cats['fun_'], cg)
    print_category("Modifiers (modifier_*)", cats['modifier_'], cg)
    print_category("External Dispatch Functions (external_fun_*)", cats['external_fun_'], cg)
    print_category("ABI Decode Functions", cats['abi_decode'], cg)
    print_category("ABI Encode Functions", cats['abi_encode'], cg)
    print_category("Other Utility Functions", cats['other'], cg)
    print_dispatch_chains(cg, defs)
    print_modifier_details(cg, defs)

    print("\n\n")
    print("=" * 100)
    print("L1ASSETROUTER.YUL - CALL GRAPH")
    print("=" * 100)

    cg2, defs2 = extract_call_graph(os.path.join(BASE, 'yul', 'L1AssetRouter.yul'))
    cats2 = categorize_funcs(defs2)

    print_category("Solidity Functions (fun_*)", cats2['fun_'], cg2)
    print_category("Modifiers (modifier_*)", cats2.get('modifier_', []), cg2)
    print_category("External Dispatch Functions (external_fun_*)", cats2['external_fun_'], cg2)
    print_category("ABI Decode Functions", cats2['abi_decode'], cg2)
    print_category("ABI Encode Functions", cats2['abi_encode'], cg2)
    print_category("Other Utility Functions", cats2['other'], cg2)
    print_dispatch_chains(cg2, defs2)

    # Analyze generated files
    analyze_generated_files('L1Nullifier')
    analyze_generated_files('L1AssetRouter')

    # Analyze Lean imports for fun_* functions
    analyze_lean_imports('L1Nullifier')
    analyze_lean_imports('L1AssetRouter')


if __name__ == '__main__':
    main()
