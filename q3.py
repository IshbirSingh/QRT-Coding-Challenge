import os

def probe(t):
    a = -0.251
    b = 0.15
    return [a + b * 4.0 * t * (1.0 - t)]
    
if __name__ == "__main__":
    t = float(input().strip())
    result = probe(t)

    with open(os.environ["OUTPUT_PATH"], "w") as f:
        f.write("\n".join(map(str, result)))
        f.write("\n")