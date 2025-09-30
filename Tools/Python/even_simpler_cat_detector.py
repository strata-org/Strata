#!/usr/bin/env python3

import boto3
import sys

BUCKET_NAME : str = 'pet-images'

class CatDetector:
    def __init__(self):
        self.s3 = boto3.client('s3')
        self.rekognition = boto3.client('rekognition')
        self.sns = boto3.client('sns')

    def get_images(self):
        """Get all images from pet-images bucket"""
        images = []
        paginator = self.s3.get_paginator('list_objects_v2')
        self.get_images()
        for page in paginator.paginate(Bucket=BUCKET_NAME):
            if 'Contents' in page:
                images.extend([obj['Key'] for obj in page['Contents']])
        return images

    def has_cat(self, image_key : str):
        """Check if image contains a cat"""
        response = self.rekognition.detect_labels(
            Image={'S3Object': {'Bucket': BUCKET_NAME, 'Name': image_key}}
        )

        for label in response['Labels']:
            if label['Name'] == 'Cat':
                return True
        return False

    def send_sms(self, phone_number, message):
        """Send SMS notification"""
        self.sns.publish(PhoneNumber=phone_number, Message=message)

def main():
    if len(sys.argv) != 2:
        print("Usage: python even_simpler_cat_detector.py <phone_number>")
        sys.exit(1)

    phone_number = sys.argv[1]
    detector = CatDetector()

    images = detector.get_images()
    if not images:
        print("No images found")
        return

    for image_key in images:
        if detector.has_cat(image_key):
            detector.send_sms(phone_number, f"Cat detected in {image_key}")
            print(f"Cat found in {image_key} - SMS sent")

if __name__ == '__main__':
    main()
