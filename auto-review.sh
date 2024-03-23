#!/usr/bin/env bash

set -e

# Check if no arguments were passed
if [ $# -eq 0 ]; then
    echo "No arguments provided. Please provide either 'mail' or 'branch'."
    exit 1
fi

pushd "$HOME/kernel/review"
case $1 in
    "mail")
        b4 mbox "$2"
        rm "$2.mbx"
        git worktree add --detach "$2" rust-next
        pushd "$2"
        b4 shazam "$2"
        git review rust-next
        popd
        git worktree remove "$2"
        ;;
    "branch")
        if [ ! $# -eq 4 ]; then
            echo "'branch' command expects exactly 3 arguments: \`branch [git-repo-url] [branch] [review-base]\`"
            exit 1
        fi
        git worktree add --detach "$3" rust-next
        pushd "$3"
        remote_name=$(git remote -v | rg "$2" | awk '{print $1}')
        if [ -z "$remote_name" ]; then
            git remote add review-tmp "$2"
            remote_name="review-tmp"
        fi
        git fetch "$remote_name"
        git checkout --detach "$remote_name/$3"
        if [ "$remote_name" = "review-tmp" ]; then
            git remote remove review-tmp
        fi
        git review "$4"
        popd
        git worktree remove "$3"
        ;;
    *)
        echo "Invalid command. Please provide either 'mail' or 'branch'."
        ;;
esac
popd
