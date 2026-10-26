#include <bits/stdc++.h>

using namespace std;

string ltrim(const string &);
string rtrim(const string &);



/*
 * Complete the 'assemble' function below.
 *
 * The function is expected to return a 2D_INTEGER_ARRAY.
 * The function accepts STRING_ARRAY pieces as parameter.
 */

vector<vector<int>> assemble(vector<string> pieces) {
    vector<vector<int>> result;
    result.reserve(pieces.size());

    for (int i = 0; i < static_cast<int>(pieces.size()); ++i) {
        // Columns: piece ID, page label, row, column.
        result.push_back({i, i, 0, 0});
    }

    return result;
}


int main()
{
    ofstream fout(getenv("OUTPUT_PATH"));

    string pieces_count_temp;
    getline(cin, pieces_count_temp);

    int pieces_count = stoi(ltrim(rtrim(pieces_count_temp)));

    vector<string> pieces(pieces_count);

    for (int i = 0; i < pieces_count; i++) {
        string pieces_item;
        getline(cin, pieces_item);

        pieces[i] = pieces_item;
    }

    vector<vector<int>> result = assemble(pieces);

    for (size_t i = 0; i < result.size(); i++) {
        for (size_t j = 0; j < result[i].size(); j++) {
            fout << result[i][j];

            if (j != result[i].size() - 1) {
                fout << " ";
            }
        }

        if (i != result.size() - 1) {
            fout << "\n";
        }
    }

    fout << "\n";

    fout.close();

    return 0;
}

string ltrim(const string &str) {
    string s(str);

    s.erase(
        s.begin(),
        find_if(s.begin(), s.end(), not1(ptr_fun<int, int>(isspace)))
    );

    return s;
}

string rtrim(const string &str) {
    string s(str);

    s.erase(
        find_if(s.rbegin(), s.rend(), not1(ptr_fun<int, int>(isspace))).base(),
        s.end()
    );

    return s;
}