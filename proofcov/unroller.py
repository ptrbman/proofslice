import re

def unroll(lines, n):
    """
    Unrolls for-loops in a C program n times.

    Args:
        lines (list of str): Lines of the C program.
        n (int): Number of times to unroll the loop.

    Returns:
        list of str: The modified lines with unrolled loops.
    """
    unrolled_lines = []
    skip_closing_brace = False  # Flag to skip the closing brace of the loop
    line_map = {} # Map new line numbers to original lines
    found_loops = 0 # We need to know how many loops we found to adjust the line map correctly
    i = 0
    while i < len(lines):
        print(f"{i} ... {len(unrolled_lines)}: {lines[i].strip()}")
        # Match a simple for loop (e.g., for (int i = 1; i <= 10; i++))
        line = lines[i]
        match = re.match(r'\s*for\s*\(\s*(int\s+)?(\w+)\s*=\s*(\d+)\s*;\s*\2\s*(<|<=)\s*(\d+)\s*;\s*\2\+\+\s*\)\s*{', line)
        if match:
            found_loops += 1
            var_name = match.group(2)
            start = int(match.group(3))
            operator = match.group(4)
            end = int(match.group(5))
            
            # Adjust the end value based on the operator
            if operator == "<=":
                end += 1
            
            # Generate unrolled loop body
            loop_body = []
            brace_count = 1
            for body_line in lines[lines.index(line) + 1:]:
                if '{' in body_line:
                    brace_count += 1
                if '}' in body_line:
                    brace_count -= 1
                if brace_count == 0:
                    skip_closing_brace = True  # Skip the closing brace
                    break
                loop_body.append(body_line)

            loop_lines = len(loop_body)
            # Unroll the loop n times or up to the loop's range
            for x in range(start, min(start + n, end)):
                for x2, body_line in enumerate(loop_body):
                    line_map[len(unrolled_lines)] = i + x2 + 1
                    print(f"Added to line map: {len(unrolled_lines)} -> {i + x2 + 1}")
                    unrolled_lines.append(body_line.replace(var_name, str(x)))
                    # Update line map
            i = i + loop_lines
        elif skip_closing_brace and line.strip() == "}":
            skip_closing_brace = False  # Skip this closing brace
        else:
            line_map[len(unrolled_lines)] = i #  Map the original line number
            print(f"Added to line map2: {len(unrolled_lines)} -> {i }")
            unrolled_lines.append(line)
        i += 1
    
    return unrolled_lines, line_map